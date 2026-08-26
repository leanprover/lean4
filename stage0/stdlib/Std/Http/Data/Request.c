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
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
lean_object* v_it_136_; lean_object* v_out_137_; lean_object* v___y_153_; uint32_t v___y_154_; lean_object* v___y_155_; uint8_t v___y_156_; lean_object* v_it_162_; lean_object* v_startInclusive_163_; lean_object* v_endExclusive_164_; 
if (lean_obj_tag(v_it_131_) == 0)
{
lean_object* v_currPos_171_; lean_object* v_searcher_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_194_; 
v_currPos_171_ = lean_ctor_get(v_it_131_, 0);
v_searcher_172_ = lean_ctor_get(v_it_131_, 1);
v_isSharedCheck_194_ = !lean_is_exclusive(v_it_131_);
if (v_isSharedCheck_194_ == 0)
{
v___x_174_ = v_it_131_;
v_isShared_175_ = v_isSharedCheck_194_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_searcher_172_);
lean_inc(v_currPos_171_);
lean_dec(v_it_131_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_194_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
uint8_t v_decide_176_; 
v_decide_176_ = lean_nat_dec_eq(v_searcher_172_, v___x_128_);
if (v_decide_176_ == 0)
{
uint32_t v___x_177_; uint8_t v___x_178_; 
lean_dec(v___x_128_);
v___x_177_ = lean_string_utf8_get_fast(v_fst_127_, v_searcher_172_);
v___x_178_ = lean_uint32_dec_eq(v___x_177_, v___x_129_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_string_utf8_next_fast(v_fst_127_, v_searcher_172_);
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
v___x_182_ = lean_apply_4(v_recur_134_, v___x_181_, v_acc_132_, lean_box(0), lean_box(0));
return v___x_182_;
}
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_slice_187_; lean_object* v_nextIt_189_; 
v___x_184_ = lean_string_utf8_next_fast(v_fst_127_, v_searcher_172_);
v___x_185_ = lean_nat_sub(v___x_184_, v_searcher_172_);
v___x_186_ = lean_nat_add(v_searcher_172_, v___x_185_);
lean_dec(v___x_185_);
v_slice_187_ = l_String_Slice_subslice_x21(v___x_130_, v_currPos_171_, v_searcher_172_);
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
v_it_162_ = v_nextIt_189_;
v_startInclusive_163_ = v_startInclusive_190_;
v_endExclusive_164_ = v_endExclusive_191_;
goto v___jp_161_;
}
}
}
else
{
lean_object* v___x_193_; 
lean_del_object(v___x_174_);
lean_dec(v_searcher_172_);
v___x_193_ = lean_box(1);
v_it_162_ = v___x_193_;
v_startInclusive_163_ = v_currPos_171_;
v_endExclusive_164_ = v___x_128_;
goto v___jp_161_;
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
if (v___y_156_ == 0)
{
lean_object* v___x_157_; 
v___x_157_ = lean_string_utf8_set(v___y_153_, v___x_125_, v___y_154_);
v_it_136_ = v___y_155_;
v_out_137_ = v___x_157_;
goto v___jp_135_;
}
else
{
uint32_t v___x_158_; uint32_t v___x_159_; lean_object* v___x_160_; 
v___x_158_ = 4294967264;
v___x_159_ = lean_uint32_add(v___y_154_, v___x_158_);
v___x_160_ = lean_string_utf8_set(v___y_153_, v___x_125_, v___x_159_);
v_it_136_ = v___y_155_;
v_out_137_ = v___x_160_;
goto v___jp_135_;
}
}
v___jp_161_:
{
lean_object* v___x_165_; uint32_t v___x_166_; uint32_t v___x_167_; uint8_t v___x_168_; 
v___x_165_ = lean_string_utf8_extract_fast(v_fst_127_, v_startInclusive_163_, v_endExclusive_164_);
lean_dec(v_endExclusive_164_);
lean_dec(v_startInclusive_163_);
v___x_166_ = lean_string_utf8_get(v___x_165_, v___x_125_);
v___x_167_ = 97;
v___x_168_ = lean_uint32_dec_le(v___x_167_, v___x_166_);
if (v___x_168_ == 0)
{
v___y_153_ = v___x_165_;
v___y_154_ = v___x_166_;
v___y_155_ = v_it_162_;
v___y_156_ = v___x_168_;
goto v___jp_152_;
}
else
{
uint32_t v___x_169_; uint8_t v___x_170_; 
v___x_169_ = 122;
v___x_170_ = lean_uint32_dec_le(v___x_166_, v___x_169_);
v___y_153_ = v___x_165_;
v___y_154_ = v___x_166_;
v___y_155_ = v_it_162_;
v___y_156_ = v___x_170_;
goto v___jp_152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__1___boxed(lean_object* v___x_195_, lean_object* v___x_196_, lean_object* v___x_197_, lean_object* v_fst_198_, lean_object* v___x_199_, lean_object* v___x_200_, lean_object* v___x_201_, lean_object* v_it_202_, lean_object* v_acc_203_, lean_object* v_hP_204_, lean_object* v_recur_205_){
_start:
{
uint32_t v___x_1547__boxed_206_; lean_object* v_res_207_; 
v___x_1547__boxed_206_ = lean_unbox_uint32(v___x_200_);
lean_dec(v___x_200_);
v_res_207_ = l_Std_Http_Request_instToStringHead___lam__1(v___x_195_, v___x_196_, v___x_197_, v_fst_198_, v___x_199_, v___x_1547__boxed_206_, v___x_201_, v_it_202_, v_acc_203_, v_hP_204_, v_recur_205_);
lean_dec_ref(v___x_201_);
lean_dec_ref(v_fst_198_);
lean_dec(v___x_197_);
lean_dec(v___x_196_);
lean_dec_ref(v___x_195_);
return v_res_207_;
}
}
static lean_object* _init_l_Std_Http_Request_instToStringHead___lam__2___closed__3(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__2));
v___x_212_ = lean_string_utf8_byte_size(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1(void){
_start:
{
uint32_t v___x_214_; lean_object* v___x_215_; 
v___x_214_ = 45;
v___x_215_ = lean_box_uint32(v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2(lean_object* v_x_216_){
_start:
{
lean_object* v_fst_217_; lean_object* v_snd_218_; lean_object* v___y_220_; lean_object* v___f_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v_it_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___f_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_fst_217_ = lean_ctor_get(v_x_216_, 0);
lean_inc_n(v_fst_217_, 2);
v_snd_218_ = lean_ctor_get(v_x_216_, 1);
lean_inc(v_snd_218_);
lean_dec_ref(v_x_216_);
v___f_224_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__1));
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_string_utf8_byte_size(v_fst_217_);
v___x_227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_227_, 0, v_fst_217_);
lean_ctor_set(v___x_227_, 1, v___x_225_);
lean_ctor_set(v___x_227_, 2, v___x_226_);
lean_inc_ref(v___x_227_);
v_it_228_ = l_String_Slice_splitToSubslice___redArg(v___x_227_, v___f_224_);
v___x_229_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__2));
v___x_230_ = lean_obj_once(&l_Std_Http_Request_instToStringHead___lam__2___closed__3, &l_Std_Http_Request_instToStringHead___lam__2___closed__3_once, _init_l_Std_Http_Request_instToStringHead___lam__2___closed__3);
v___x_231_ = l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1;
v___f_232_ = lean_alloc_closure((void*)(l_Std_Http_Request_instToStringHead___lam__1___boxed), 11, 7);
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
v___x_235_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_220_ = v___x_235_;
goto v___jp_219_;
}
else
{
lean_object* v_val_236_; 
v_val_236_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_val_236_);
lean_dec_ref_known(v___x_234_, 1);
v___y_220_ = v_val_236_;
goto v___jp_219_;
}
v___jp_219_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__0));
v___x_222_ = lean_string_append(v___y_220_, v___x_221_);
v___x_223_ = lean_string_append(v___x_222_, v_snd_218_);
lean_dec(v_snd_218_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__4(lean_object* v___f_310_, lean_object* v___f_311_, lean_object* v___f_312_, lean_object* v_req_313_){
_start:
{
uint8_t v_method_314_; uint8_t v_version_315_; lean_object* v_uri_316_; lean_object* v_headers_317_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v_port_420_; lean_object* v___y_421_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v_host_437_; lean_object* v_port_438_; lean_object* v___y_439_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v_port_461_; lean_object* v___y_462_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v_host_473_; lean_object* v_port_474_; lean_object* v___y_475_; lean_object* v___y_486_; 
v_method_314_ = lean_ctor_get_uint8(v_req_313_, sizeof(void*)*2);
v_version_315_ = lean_ctor_get_uint8(v_req_313_, sizeof(void*)*2 + 1);
v_uri_316_ = lean_ctor_get(v_req_313_, 0);
lean_inc(v_uri_316_);
v_headers_317_ = lean_ctor_get(v_req_313_, 1);
lean_inc_ref(v_headers_317_);
lean_dec_ref(v_req_313_);
switch(v_method_314_)
{
case 0:
{
lean_object* v___x_558_; 
v___x_558_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__24));
v___y_486_ = v___x_558_;
goto v___jp_485_;
}
case 1:
{
lean_object* v___x_559_; 
v___x_559_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__25));
v___y_486_ = v___x_559_;
goto v___jp_485_;
}
case 2:
{
lean_object* v___x_560_; 
v___x_560_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__26));
v___y_486_ = v___x_560_;
goto v___jp_485_;
}
case 3:
{
lean_object* v___x_561_; 
v___x_561_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__27));
v___y_486_ = v___x_561_;
goto v___jp_485_;
}
case 4:
{
lean_object* v___x_562_; 
v___x_562_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__28));
v___y_486_ = v___x_562_;
goto v___jp_485_;
}
case 5:
{
lean_object* v___x_563_; 
v___x_563_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__29));
v___y_486_ = v___x_563_;
goto v___jp_485_;
}
case 6:
{
lean_object* v___x_564_; 
v___x_564_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__30));
v___y_486_ = v___x_564_;
goto v___jp_485_;
}
case 7:
{
lean_object* v___x_565_; 
v___x_565_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__31));
v___y_486_ = v___x_565_;
goto v___jp_485_;
}
case 8:
{
lean_object* v___x_566_; 
v___x_566_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__32));
v___y_486_ = v___x_566_;
goto v___jp_485_;
}
case 9:
{
lean_object* v___x_567_; 
v___x_567_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__33));
v___y_486_ = v___x_567_;
goto v___jp_485_;
}
case 10:
{
lean_object* v___x_568_; 
v___x_568_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__34));
v___y_486_ = v___x_568_;
goto v___jp_485_;
}
case 11:
{
lean_object* v___x_569_; 
v___x_569_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__35));
v___y_486_ = v___x_569_;
goto v___jp_485_;
}
case 12:
{
lean_object* v___x_570_; 
v___x_570_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__36));
v___y_486_ = v___x_570_;
goto v___jp_485_;
}
case 13:
{
lean_object* v___x_571_; 
v___x_571_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__37));
v___y_486_ = v___x_571_;
goto v___jp_485_;
}
case 14:
{
lean_object* v___x_572_; 
v___x_572_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__38));
v___y_486_ = v___x_572_;
goto v___jp_485_;
}
case 15:
{
lean_object* v___x_573_; 
v___x_573_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__39));
v___y_486_ = v___x_573_;
goto v___jp_485_;
}
case 16:
{
lean_object* v___x_574_; 
v___x_574_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__40));
v___y_486_ = v___x_574_;
goto v___jp_485_;
}
case 17:
{
lean_object* v___x_575_; 
v___x_575_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__41));
v___y_486_ = v___x_575_;
goto v___jp_485_;
}
case 18:
{
lean_object* v___x_576_; 
v___x_576_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__42));
v___y_486_ = v___x_576_;
goto v___jp_485_;
}
case 19:
{
lean_object* v___x_577_; 
v___x_577_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__43));
v___y_486_ = v___x_577_;
goto v___jp_485_;
}
case 20:
{
lean_object* v___x_578_; 
v___x_578_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__44));
v___y_486_ = v___x_578_;
goto v___jp_485_;
}
case 21:
{
lean_object* v___x_579_; 
v___x_579_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__45));
v___y_486_ = v___x_579_;
goto v___jp_485_;
}
case 22:
{
lean_object* v___x_580_; 
v___x_580_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__46));
v___y_486_ = v___x_580_;
goto v___jp_485_;
}
case 23:
{
lean_object* v___x_581_; 
v___x_581_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__47));
v___y_486_ = v___x_581_;
goto v___jp_485_;
}
case 24:
{
lean_object* v___x_582_; 
v___x_582_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__48));
v___y_486_ = v___x_582_;
goto v___jp_485_;
}
case 25:
{
lean_object* v___x_583_; 
v___x_583_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__49));
v___y_486_ = v___x_583_;
goto v___jp_485_;
}
case 26:
{
lean_object* v___x_584_; 
v___x_584_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__50));
v___y_486_ = v___x_584_;
goto v___jp_485_;
}
case 27:
{
lean_object* v___x_585_; 
v___x_585_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__51));
v___y_486_ = v___x_585_;
goto v___jp_485_;
}
case 28:
{
lean_object* v___x_586_; 
v___x_586_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__52));
v___y_486_ = v___x_586_;
goto v___jp_485_;
}
case 29:
{
lean_object* v___x_587_; 
v___x_587_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__53));
v___y_486_ = v___x_587_;
goto v___jp_485_;
}
case 30:
{
lean_object* v___x_588_; 
v___x_588_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__54));
v___y_486_ = v___x_588_;
goto v___jp_485_;
}
case 31:
{
lean_object* v___x_589_; 
v___x_589_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__55));
v___y_486_ = v___x_589_;
goto v___jp_485_;
}
case 32:
{
lean_object* v___x_590_; 
v___x_590_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__56));
v___y_486_ = v___x_590_;
goto v___jp_485_;
}
case 33:
{
lean_object* v___x_591_; 
v___x_591_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__57));
v___y_486_ = v___x_591_;
goto v___jp_485_;
}
case 34:
{
lean_object* v___x_592_; 
v___x_592_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__58));
v___y_486_ = v___x_592_;
goto v___jp_485_;
}
case 35:
{
lean_object* v___x_593_; 
v___x_593_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__59));
v___y_486_ = v___x_593_;
goto v___jp_485_;
}
case 36:
{
lean_object* v___x_594_; 
v___x_594_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__60));
v___y_486_ = v___x_594_;
goto v___jp_485_;
}
case 37:
{
lean_object* v___x_595_; 
v___x_595_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__61));
v___y_486_ = v___x_595_;
goto v___jp_485_;
}
case 38:
{
lean_object* v___x_596_; 
v___x_596_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__62));
v___y_486_ = v___x_596_;
goto v___jp_485_;
}
default: 
{
lean_object* v___x_597_; 
v___x_597_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__63));
v___y_486_ = v___x_597_;
goto v___jp_485_;
}
}
v___jp_318_:
{
lean_object* v_entries_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; size_t v_sz_326_; size_t v___x_327_; lean_object* v_pairs_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_entries_321_ = lean_ctor_get(v_headers_317_, 0);
lean_inc_ref(v_entries_321_);
lean_dec_ref(v_headers_317_);
v___x_322_ = lean_string_append(v___y_319_, v___y_320_);
v___x_323_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__0));
v___x_324_ = lean_string_append(v___x_322_, v___x_323_);
v___x_325_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_326_ = lean_array_size(v_entries_321_);
v___x_327_ = ((size_t)0ULL);
v_pairs_328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_325_, v___f_310_, v_sz_326_, v___x_327_, v_entries_321_);
v___x_329_ = lean_array_to_list(v_pairs_328_);
v___x_330_ = l_String_intercalate(v___x_323_, v___x_329_);
v___x_331_ = lean_string_append(v___x_324_, v___x_330_);
lean_dec_ref(v___x_330_);
v___x_332_ = lean_string_append(v___x_331_, v___x_323_);
return v___x_332_;
}
v___jp_333_:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_string_append(v___y_334_, v___y_336_);
lean_dec_ref(v___y_336_);
v___x_338_ = lean_string_append(v___x_337_, v___y_335_);
switch(v_version_315_)
{
case 0:
{
lean_object* v___x_339_; 
v___x_339_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__11));
v___y_319_ = v___x_338_;
v___y_320_ = v___x_339_;
goto v___jp_318_;
}
case 1:
{
lean_object* v___x_340_; 
v___x_340_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__12));
v___y_319_ = v___x_338_;
v___y_320_ = v___x_340_;
goto v___jp_318_;
}
case 2:
{
lean_object* v___x_341_; 
v___x_341_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__13));
v___y_319_ = v___x_338_;
v___y_320_ = v___x_341_;
goto v___jp_318_;
}
default: 
{
lean_object* v___x_342_; 
v___x_342_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__14));
v___y_319_ = v___x_338_;
v___y_320_ = v___x_342_;
goto v___jp_318_;
}
}
}
v___jp_343_:
{
lean_object* v_queryStr_348_; lean_object* v___x_349_; 
v_queryStr_348_ = l_Std_Http_URI_Query_formatOption(v___y_346_);
v___x_349_ = lean_string_append(v___y_347_, v_queryStr_348_);
lean_dec_ref(v_queryStr_348_);
v___y_334_ = v___y_344_;
v___y_335_ = v___y_345_;
v___y_336_ = v___x_349_;
goto v___jp_333_;
}
v___jp_350_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_358_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_359_ = lean_string_append(v___y_352_, v___x_358_);
v___x_360_ = lean_string_append(v___x_359_, v___y_354_);
lean_dec_ref(v___y_354_);
v___x_361_ = lean_string_append(v___x_360_, v___y_355_);
lean_dec_ref(v___y_355_);
v___x_362_ = lean_string_append(v___x_361_, v___y_356_);
lean_dec_ref(v___y_356_);
v___x_363_ = lean_string_append(v___x_362_, v___y_357_);
lean_dec_ref(v___y_357_);
v___y_334_ = v___y_351_;
v___y_335_ = v___y_353_;
v___y_336_ = v___x_363_;
goto v___jp_333_;
}
v___jp_364_:
{
lean_object* v_queryPart_372_; 
v_queryPart_372_ = l_Std_Http_URI_Query_formatOption(v___y_370_);
if (lean_obj_tag(v___y_367_) == 0)
{
lean_object* v___x_373_; 
v___x_373_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_351_ = v___y_365_;
v___y_352_ = v___y_366_;
v___y_353_ = v___y_368_;
v___y_354_ = v___y_369_;
v___y_355_ = v___y_371_;
v___y_356_ = v_queryPart_372_;
v___y_357_ = v___x_373_;
goto v___jp_350_;
}
else
{
lean_object* v_val_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_val_374_ = lean_ctor_get(v___y_367_, 0);
lean_inc(v_val_374_);
lean_dec_ref_known(v___y_367_, 1);
v___x_375_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__16));
v___x_376_ = l_Std_Http_URI_EncodedFragment_encode(v_val_374_);
lean_dec(v_val_374_);
v___x_377_ = lean_string_from_utf8_unchecked(v___x_376_);
v___x_378_ = lean_string_append(v___x_375_, v___x_377_);
lean_dec_ref(v___x_377_);
v___y_351_ = v___y_365_;
v___y_352_ = v___y_366_;
v___y_353_ = v___y_368_;
v___y_354_ = v___y_369_;
v___y_355_ = v___y_371_;
v___y_356_ = v_queryPart_372_;
v___y_357_ = v___x_378_;
goto v___jp_350_;
}
}
v___jp_379_:
{
lean_object* v_segments_387_; uint8_t v_absolute_388_; lean_object* v___x_389_; lean_object* v___x_390_; size_t v_sz_391_; size_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_result_395_; 
v_segments_387_ = lean_ctor_get(v___y_380_, 0);
lean_inc_ref(v_segments_387_);
v_absolute_388_ = lean_ctor_get_uint8(v___y_380_, sizeof(void*)*1);
lean_dec_ref(v___y_380_);
v___x_389_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_390_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_391_ = lean_array_size(v_segments_387_);
v___x_392_ = ((size_t)0ULL);
v___x_393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_390_, v___f_311_, v_sz_391_, v___x_392_, v_segments_387_);
v___x_394_ = lean_array_to_list(v___x_393_);
v_result_395_ = l_String_intercalate(v___x_389_, v___x_394_);
if (v_absolute_388_ == 0)
{
v___y_365_ = v___y_381_;
v___y_366_ = v___y_382_;
v___y_367_ = v___y_384_;
v___y_368_ = v___y_383_;
v___y_369_ = v___y_386_;
v___y_370_ = v___y_385_;
v___y_371_ = v_result_395_;
goto v___jp_364_;
}
else
{
lean_object* v___x_396_; 
v___x_396_ = lean_string_append(v___x_389_, v_result_395_);
lean_dec_ref(v_result_395_);
v___y_365_ = v___y_381_;
v___y_366_ = v___y_382_;
v___y_367_ = v___y_384_;
v___y_368_ = v___y_383_;
v___y_369_ = v___y_386_;
v___y_370_ = v___y_385_;
v___y_371_ = v___x_396_;
goto v___jp_364_;
}
}
v___jp_397_:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_string_append(v___y_402_, v___y_399_);
lean_dec_ref(v___y_399_);
v___x_409_ = lean_string_append(v___x_408_, v___y_407_);
lean_dec_ref(v___y_407_);
lean_inc_ref(v___y_398_);
v___x_410_ = lean_string_append(v___y_398_, v___x_409_);
lean_dec_ref(v___x_409_);
v___y_380_ = v___y_401_;
v___y_381_ = v___y_400_;
v___y_382_ = v___y_403_;
v___y_383_ = v___y_405_;
v___y_384_ = v___y_404_;
v___y_385_ = v___y_406_;
v___y_386_ = v___x_410_;
goto v___jp_379_;
}
v___jp_411_:
{
switch(lean_obj_tag(v_port_420_))
{
case 0:
{
lean_object* v___x_422_; 
v___x_422_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_398_ = v___y_412_;
v___y_399_ = v___y_421_;
v___y_400_ = v___y_415_;
v___y_401_ = v___y_414_;
v___y_402_ = v___y_413_;
v___y_403_ = v___y_416_;
v___y_404_ = v___y_418_;
v___y_405_ = v___y_417_;
v___y_406_ = v___y_419_;
v___y_407_ = v___x_422_;
goto v___jp_397_;
}
case 1:
{
lean_object* v___x_423_; 
v___x_423_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_398_ = v___y_412_;
v___y_399_ = v___y_421_;
v___y_400_ = v___y_415_;
v___y_401_ = v___y_414_;
v___y_402_ = v___y_413_;
v___y_403_ = v___y_416_;
v___y_404_ = v___y_418_;
v___y_405_ = v___y_417_;
v___y_406_ = v___y_419_;
v___y_407_ = v___x_423_;
goto v___jp_397_;
}
default: 
{
uint16_t v_port_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_port_424_ = lean_ctor_get_uint16(v_port_420_, 0);
lean_dec_ref_known(v_port_420_, 0);
v___x_425_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_426_ = lean_uint16_to_nat(v_port_424_);
v___x_427_ = l_Nat_reprFast(v___x_426_);
v___x_428_ = lean_string_append(v___x_425_, v___x_427_);
lean_dec_ref(v___x_427_);
v___y_398_ = v___y_412_;
v___y_399_ = v___y_421_;
v___y_400_ = v___y_415_;
v___y_401_ = v___y_414_;
v___y_402_ = v___y_413_;
v___y_403_ = v___y_416_;
v___y_404_ = v___y_418_;
v___y_405_ = v___y_417_;
v___y_406_ = v___y_419_;
v___y_407_ = v___x_428_;
goto v___jp_397_;
}
}
}
v___jp_429_:
{
switch(lean_obj_tag(v_host_437_))
{
case 0:
{
lean_object* v_name_440_; 
v_name_440_ = lean_ctor_get(v_host_437_, 0);
lean_inc_ref(v_name_440_);
lean_dec_ref_known(v_host_437_, 1);
v___y_412_ = v___y_430_;
v___y_413_ = v___y_439_;
v___y_414_ = v___y_432_;
v___y_415_ = v___y_431_;
v___y_416_ = v___y_433_;
v___y_417_ = v___y_435_;
v___y_418_ = v___y_434_;
v___y_419_ = v___y_436_;
v_port_420_ = v_port_438_;
v___y_421_ = v_name_440_;
goto v___jp_411_;
}
case 1:
{
lean_object* v_ipv4_441_; lean_object* v___x_442_; 
v_ipv4_441_ = lean_ctor_get(v_host_437_, 0);
lean_inc_ref(v_ipv4_441_);
lean_dec_ref_known(v_host_437_, 1);
v___x_442_ = lean_uv_ntop_v4(v_ipv4_441_);
lean_dec_ref(v_ipv4_441_);
v___y_412_ = v___y_430_;
v___y_413_ = v___y_439_;
v___y_414_ = v___y_432_;
v___y_415_ = v___y_431_;
v___y_416_ = v___y_433_;
v___y_417_ = v___y_435_;
v___y_418_ = v___y_434_;
v___y_419_ = v___y_436_;
v_port_420_ = v_port_438_;
v___y_421_ = v___x_442_;
goto v___jp_411_;
}
default: 
{
lean_object* v_ipv6_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v_ipv6_443_ = lean_ctor_get(v_host_437_, 0);
lean_inc_ref(v_ipv6_443_);
lean_dec_ref_known(v_host_437_, 1);
v___x_444_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_445_ = lean_uv_ntop_v6(v_ipv6_443_);
lean_dec_ref(v_ipv6_443_);
v___x_446_ = lean_string_append(v___x_444_, v___x_445_);
lean_dec_ref(v___x_445_);
v___x_447_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_448_ = lean_string_append(v___x_446_, v___x_447_);
v___y_412_ = v___y_430_;
v___y_413_ = v___y_439_;
v___y_414_ = v___y_432_;
v___y_415_ = v___y_431_;
v___y_416_ = v___y_433_;
v___y_417_ = v___y_435_;
v___y_418_ = v___y_434_;
v___y_419_ = v___y_436_;
v_port_420_ = v_port_438_;
v___y_421_ = v___x_448_;
goto v___jp_411_;
}
}
}
v___jp_449_:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_string_append(v___y_450_, v___y_453_);
lean_dec_ref(v___y_453_);
v___x_456_ = lean_string_append(v___x_455_, v___y_454_);
lean_dec_ref(v___y_454_);
v___y_334_ = v___y_451_;
v___y_335_ = v___y_452_;
v___y_336_ = v___x_456_;
goto v___jp_333_;
}
v___jp_457_:
{
switch(lean_obj_tag(v_port_461_))
{
case 0:
{
lean_object* v___x_463_; 
v___x_463_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_450_ = v___y_458_;
v___y_451_ = v___y_459_;
v___y_452_ = v___y_460_;
v___y_453_ = v___y_462_;
v___y_454_ = v___x_463_;
goto v___jp_449_;
}
case 1:
{
lean_object* v___x_464_; 
v___x_464_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_450_ = v___y_458_;
v___y_451_ = v___y_459_;
v___y_452_ = v___y_460_;
v___y_453_ = v___y_462_;
v___y_454_ = v___x_464_;
goto v___jp_449_;
}
default: 
{
uint16_t v_port_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_port_465_ = lean_ctor_get_uint16(v_port_461_, 0);
lean_dec_ref_known(v_port_461_, 0);
v___x_466_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_467_ = lean_uint16_to_nat(v_port_465_);
v___x_468_ = l_Nat_reprFast(v___x_467_);
v___x_469_ = lean_string_append(v___x_466_, v___x_468_);
lean_dec_ref(v___x_468_);
v___y_450_ = v___y_458_;
v___y_451_ = v___y_459_;
v___y_452_ = v___y_460_;
v___y_453_ = v___y_462_;
v___y_454_ = v___x_469_;
goto v___jp_449_;
}
}
}
v___jp_470_:
{
switch(lean_obj_tag(v_host_473_))
{
case 0:
{
lean_object* v_name_476_; 
v_name_476_ = lean_ctor_get(v_host_473_, 0);
lean_inc_ref(v_name_476_);
lean_dec_ref_known(v_host_473_, 1);
v___y_458_ = v___y_475_;
v___y_459_ = v___y_471_;
v___y_460_ = v___y_472_;
v_port_461_ = v_port_474_;
v___y_462_ = v_name_476_;
goto v___jp_457_;
}
case 1:
{
lean_object* v_ipv4_477_; lean_object* v___x_478_; 
v_ipv4_477_ = lean_ctor_get(v_host_473_, 0);
lean_inc_ref(v_ipv4_477_);
lean_dec_ref_known(v_host_473_, 1);
v___x_478_ = lean_uv_ntop_v4(v_ipv4_477_);
lean_dec_ref(v_ipv4_477_);
v___y_458_ = v___y_475_;
v___y_459_ = v___y_471_;
v___y_460_ = v___y_472_;
v_port_461_ = v_port_474_;
v___y_462_ = v___x_478_;
goto v___jp_457_;
}
default: 
{
lean_object* v_ipv6_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_ipv6_479_ = lean_ctor_get(v_host_473_, 0);
lean_inc_ref(v_ipv6_479_);
lean_dec_ref_known(v_host_473_, 1);
v___x_480_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_481_ = lean_uv_ntop_v6(v_ipv6_479_);
lean_dec_ref(v_ipv6_479_);
v___x_482_ = lean_string_append(v___x_480_, v___x_481_);
lean_dec_ref(v___x_481_);
v___x_483_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_484_ = lean_string_append(v___x_482_, v___x_483_);
v___y_458_ = v___y_475_;
v___y_459_ = v___y_471_;
v___y_460_ = v___y_472_;
v_port_461_ = v_port_474_;
v___y_462_ = v___x_484_;
goto v___jp_457_;
}
}
}
v___jp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__20));
lean_inc_ref(v___y_486_);
v___x_488_ = lean_string_append(v___y_486_, v___x_487_);
switch(lean_obj_tag(v_uri_316_))
{
case 0:
{
lean_object* v_path_489_; lean_object* v_query_490_; lean_object* v_segments_491_; uint8_t v_absolute_492_; lean_object* v___x_493_; lean_object* v___x_494_; size_t v_sz_495_; size_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v_result_499_; 
lean_dec_ref(v___f_311_);
v_path_489_ = lean_ctor_get(v_uri_316_, 0);
lean_inc_ref(v_path_489_);
v_query_490_ = lean_ctor_get(v_uri_316_, 1);
lean_inc(v_query_490_);
lean_dec_ref_known(v_uri_316_, 2);
v_segments_491_ = lean_ctor_get(v_path_489_, 0);
lean_inc_ref(v_segments_491_);
v_absolute_492_ = lean_ctor_get_uint8(v_path_489_, sizeof(void*)*1);
lean_dec_ref(v_path_489_);
v___x_493_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_494_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_495_ = lean_array_size(v_segments_491_);
v___x_496_ = ((size_t)0ULL);
v___x_497_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_494_, v___f_312_, v_sz_495_, v___x_496_, v_segments_491_);
v___x_498_ = lean_array_to_list(v___x_497_);
v_result_499_ = l_String_intercalate(v___x_493_, v___x_498_);
if (v_absolute_492_ == 0)
{
v___y_344_ = v___x_488_;
v___y_345_ = v___x_487_;
v___y_346_ = v_query_490_;
v___y_347_ = v_result_499_;
goto v___jp_343_;
}
else
{
lean_object* v___x_500_; 
v___x_500_ = lean_string_append(v___x_493_, v_result_499_);
lean_dec_ref(v_result_499_);
v___y_344_ = v___x_488_;
v___y_345_ = v___x_487_;
v___y_346_ = v_query_490_;
v___y_347_ = v___x_500_;
goto v___jp_343_;
}
}
case 1:
{
lean_object* v_uri_501_; lean_object* v_authority_502_; 
lean_dec_ref(v___f_312_);
v_uri_501_ = lean_ctor_get(v_uri_316_, 0);
lean_inc_ref(v_uri_501_);
lean_dec_ref_known(v_uri_316_, 1);
v_authority_502_ = lean_ctor_get(v_uri_501_, 1);
if (lean_obj_tag(v_authority_502_) == 0)
{
lean_object* v_scheme_503_; lean_object* v_path_504_; lean_object* v_query_505_; lean_object* v_fragment_506_; lean_object* v___x_507_; 
v_scheme_503_ = lean_ctor_get(v_uri_501_, 0);
lean_inc_ref(v_scheme_503_);
v_path_504_ = lean_ctor_get(v_uri_501_, 2);
lean_inc_ref(v_path_504_);
v_query_505_ = lean_ctor_get(v_uri_501_, 3);
lean_inc(v_query_505_);
v_fragment_506_ = lean_ctor_get(v_uri_501_, 4);
lean_inc(v_fragment_506_);
lean_dec_ref(v_uri_501_);
v___x_507_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_380_ = v_path_504_;
v___y_381_ = v___x_488_;
v___y_382_ = v_scheme_503_;
v___y_383_ = v___x_487_;
v___y_384_ = v_fragment_506_;
v___y_385_ = v_query_505_;
v___y_386_ = v___x_507_;
goto v___jp_379_;
}
else
{
lean_object* v_val_508_; lean_object* v_scheme_509_; lean_object* v_path_510_; lean_object* v_query_511_; lean_object* v_fragment_512_; lean_object* v_userInfo_513_; lean_object* v_host_514_; lean_object* v_port_515_; lean_object* v___x_516_; 
v_val_508_ = lean_ctor_get(v_authority_502_, 0);
lean_inc(v_val_508_);
v_scheme_509_ = lean_ctor_get(v_uri_501_, 0);
lean_inc_ref(v_scheme_509_);
v_path_510_ = lean_ctor_get(v_uri_501_, 2);
lean_inc_ref(v_path_510_);
v_query_511_ = lean_ctor_get(v_uri_501_, 3);
lean_inc(v_query_511_);
v_fragment_512_ = lean_ctor_get(v_uri_501_, 4);
lean_inc(v_fragment_512_);
lean_dec_ref(v_uri_501_);
v_userInfo_513_ = lean_ctor_get(v_val_508_, 0);
lean_inc(v_userInfo_513_);
v_host_514_ = lean_ctor_get(v_val_508_, 1);
lean_inc_ref(v_host_514_);
v_port_515_ = lean_ctor_get(v_val_508_, 2);
lean_inc(v_port_515_);
lean_dec(v_val_508_);
v___x_516_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__21));
if (lean_obj_tag(v_userInfo_513_) == 0)
{
lean_object* v___x_517_; 
v___x_517_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_430_ = v___x_516_;
v___y_431_ = v___x_488_;
v___y_432_ = v_path_510_;
v___y_433_ = v_scheme_509_;
v___y_434_ = v_fragment_512_;
v___y_435_ = v___x_487_;
v___y_436_ = v_query_511_;
v_host_437_ = v_host_514_;
v_port_438_ = v_port_515_;
v___y_439_ = v___x_517_;
goto v___jp_429_;
}
else
{
lean_object* v_val_518_; lean_object* v_password_519_; 
v_val_518_ = lean_ctor_get(v_userInfo_513_, 0);
lean_inc(v_val_518_);
lean_dec_ref_known(v_userInfo_513_, 1);
v_password_519_ = lean_ctor_get(v_val_518_, 1);
if (lean_obj_tag(v_password_519_) == 0)
{
lean_object* v_username_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_username_520_ = lean_ctor_get(v_val_518_, 0);
lean_inc_ref(v_username_520_);
lean_dec(v_val_518_);
v___x_521_ = lean_string_from_utf8_unchecked(v_username_520_);
v___x_522_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_523_ = lean_string_append(v___x_521_, v___x_522_);
v___y_430_ = v___x_516_;
v___y_431_ = v___x_488_;
v___y_432_ = v_path_510_;
v___y_433_ = v_scheme_509_;
v___y_434_ = v_fragment_512_;
v___y_435_ = v___x_487_;
v___y_436_ = v_query_511_;
v_host_437_ = v_host_514_;
v_port_438_ = v_port_515_;
v___y_439_ = v___x_523_;
goto v___jp_429_;
}
else
{
lean_object* v_username_524_; lean_object* v_val_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
lean_inc_ref(v_password_519_);
v_username_524_ = lean_ctor_get(v_val_518_, 0);
lean_inc_ref(v_username_524_);
lean_dec(v_val_518_);
v_val_525_ = lean_ctor_get(v_password_519_, 0);
lean_inc(v_val_525_);
lean_dec_ref_known(v_password_519_, 1);
v___x_526_ = lean_string_from_utf8_unchecked(v_username_524_);
v___x_527_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_528_ = lean_string_append(v___x_526_, v___x_527_);
v___x_529_ = lean_string_from_utf8_unchecked(v_val_525_);
v___x_530_ = lean_string_append(v___x_528_, v___x_529_);
lean_dec_ref(v___x_529_);
v___x_531_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_532_ = lean_string_append(v___x_530_, v___x_531_);
v___y_430_ = v___x_516_;
v___y_431_ = v___x_488_;
v___y_432_ = v_path_510_;
v___y_433_ = v_scheme_509_;
v___y_434_ = v_fragment_512_;
v___y_435_ = v___x_487_;
v___y_436_ = v_query_511_;
v_host_437_ = v_host_514_;
v_port_438_ = v_port_515_;
v___y_439_ = v___x_532_;
goto v___jp_429_;
}
}
}
}
case 2:
{
lean_object* v_authority_533_; lean_object* v_userInfo_534_; 
lean_dec_ref(v___f_312_);
lean_dec_ref(v___f_311_);
v_authority_533_ = lean_ctor_get(v_uri_316_, 0);
lean_inc_ref(v_authority_533_);
lean_dec_ref_known(v_uri_316_, 1);
v_userInfo_534_ = lean_ctor_get(v_authority_533_, 0);
if (lean_obj_tag(v_userInfo_534_) == 0)
{
lean_object* v_host_535_; lean_object* v_port_536_; lean_object* v___x_537_; 
v_host_535_ = lean_ctor_get(v_authority_533_, 1);
lean_inc_ref(v_host_535_);
v_port_536_ = lean_ctor_get(v_authority_533_, 2);
lean_inc(v_port_536_);
lean_dec_ref(v_authority_533_);
v___x_537_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_471_ = v___x_488_;
v___y_472_ = v___x_487_;
v_host_473_ = v_host_535_;
v_port_474_ = v_port_536_;
v___y_475_ = v___x_537_;
goto v___jp_470_;
}
else
{
lean_object* v_val_538_; lean_object* v_password_539_; 
v_val_538_ = lean_ctor_get(v_userInfo_534_, 0);
lean_inc(v_val_538_);
v_password_539_ = lean_ctor_get(v_val_538_, 1);
if (lean_obj_tag(v_password_539_) == 0)
{
lean_object* v_host_540_; lean_object* v_port_541_; lean_object* v_username_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v_host_540_ = lean_ctor_get(v_authority_533_, 1);
lean_inc_ref(v_host_540_);
v_port_541_ = lean_ctor_get(v_authority_533_, 2);
lean_inc(v_port_541_);
lean_dec_ref(v_authority_533_);
v_username_542_ = lean_ctor_get(v_val_538_, 0);
lean_inc_ref(v_username_542_);
lean_dec(v_val_538_);
v___x_543_ = lean_string_from_utf8_unchecked(v_username_542_);
v___x_544_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_545_ = lean_string_append(v___x_543_, v___x_544_);
v___y_471_ = v___x_488_;
v___y_472_ = v___x_487_;
v_host_473_ = v_host_540_;
v_port_474_ = v_port_541_;
v___y_475_ = v___x_545_;
goto v___jp_470_;
}
else
{
lean_object* v_host_546_; lean_object* v_port_547_; lean_object* v_username_548_; lean_object* v_val_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_inc_ref(v_password_539_);
v_host_546_ = lean_ctor_get(v_authority_533_, 1);
lean_inc_ref(v_host_546_);
v_port_547_ = lean_ctor_get(v_authority_533_, 2);
lean_inc(v_port_547_);
lean_dec_ref(v_authority_533_);
v_username_548_ = lean_ctor_get(v_val_538_, 0);
lean_inc_ref(v_username_548_);
lean_dec(v_val_538_);
v_val_549_ = lean_ctor_get(v_password_539_, 0);
lean_inc(v_val_549_);
lean_dec_ref_known(v_password_539_, 1);
v___x_550_ = lean_string_from_utf8_unchecked(v_username_548_);
v___x_551_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_552_ = lean_string_append(v___x_550_, v___x_551_);
v___x_553_ = lean_string_from_utf8_unchecked(v_val_549_);
v___x_554_ = lean_string_append(v___x_552_, v___x_553_);
lean_dec_ref(v___x_553_);
v___x_555_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_556_ = lean_string_append(v___x_554_, v___x_555_);
v___y_471_ = v___x_488_;
v___y_472_ = v___x_487_;
v_host_473_ = v_host_546_;
v_port_474_ = v_port_547_;
v___y_475_ = v___x_556_;
goto v___jp_470_;
}
}
}
default: 
{
lean_object* v___x_557_; 
lean_dec_ref(v___f_312_);
lean_dec_ref(v___f_311_);
v___x_557_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__23));
v___y_334_ = v___x_488_;
v___y_335_ = v___x_487_;
v___y_336_ = v___x_557_;
goto v___jp_333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1(lean_object* v___x_604_, lean_object* v___x_605_, lean_object* v___x_606_, lean_object* v_name_607_, lean_object* v___x_608_, uint32_t v___x_609_, lean_object* v___x_610_, lean_object* v_it_611_, lean_object* v_acc_612_, lean_object* v_hP_613_, lean_object* v_recur_614_){
_start:
{
lean_object* v_it_616_; lean_object* v_out_617_; lean_object* v___y_633_; uint32_t v___y_634_; lean_object* v___y_635_; uint8_t v___y_636_; lean_object* v_it_642_; lean_object* v_startInclusive_643_; lean_object* v_endExclusive_644_; 
if (lean_obj_tag(v_it_611_) == 0)
{
lean_object* v_currPos_651_; lean_object* v_searcher_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_674_; 
v_currPos_651_ = lean_ctor_get(v_it_611_, 0);
v_searcher_652_ = lean_ctor_get(v_it_611_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v_it_611_);
if (v_isSharedCheck_674_ == 0)
{
v___x_654_ = v_it_611_;
v_isShared_655_ = v_isSharedCheck_674_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_searcher_652_);
lean_inc(v_currPos_651_);
lean_dec(v_it_611_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_674_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
uint8_t v_decide_656_; 
v_decide_656_ = lean_nat_dec_eq(v_searcher_652_, v___x_608_);
if (v_decide_656_ == 0)
{
uint32_t v___x_657_; uint8_t v___x_658_; 
lean_dec(v___x_608_);
v___x_657_ = lean_string_utf8_get_fast(v_name_607_, v_searcher_652_);
v___x_658_ = lean_uint32_dec_eq(v___x_657_, v___x_609_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_string_utf8_next_fast(v_name_607_, v_searcher_652_);
lean_dec(v_searcher_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v___x_659_);
v___x_661_ = v___x_654_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_currPos_651_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_659_);
v___x_661_ = v_reuseFailAlloc_663_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; 
v___x_662_ = lean_apply_4(v_recur_614_, v___x_661_, v_acc_612_, lean_box(0), lean_box(0));
return v___x_662_;
}
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v_slice_667_; lean_object* v_nextIt_669_; 
v___x_664_ = lean_string_utf8_next_fast(v_name_607_, v_searcher_652_);
v___x_665_ = lean_nat_sub(v___x_664_, v_searcher_652_);
v___x_666_ = lean_nat_add(v_searcher_652_, v___x_665_);
lean_dec(v___x_665_);
v_slice_667_ = l_String_Slice_subslice_x21(v___x_610_, v_currPos_651_, v_searcher_652_);
lean_inc(v___x_666_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v___x_666_);
lean_ctor_set(v___x_654_, 0, v___x_666_);
v_nextIt_669_ = v___x_654_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v___x_666_);
v_nextIt_669_ = v_reuseFailAlloc_672_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v_startInclusive_670_; lean_object* v_endExclusive_671_; 
v_startInclusive_670_ = lean_ctor_get(v_slice_667_, 0);
lean_inc(v_startInclusive_670_);
v_endExclusive_671_ = lean_ctor_get(v_slice_667_, 1);
lean_inc(v_endExclusive_671_);
lean_dec_ref(v_slice_667_);
v_it_642_ = v_nextIt_669_;
v_startInclusive_643_ = v_startInclusive_670_;
v_endExclusive_644_ = v_endExclusive_671_;
goto v___jp_641_;
}
}
}
else
{
lean_object* v___x_673_; 
lean_del_object(v___x_654_);
lean_dec(v_searcher_652_);
v___x_673_ = lean_box(1);
v_it_642_ = v___x_673_;
v_startInclusive_643_ = v_currPos_651_;
v_endExclusive_644_ = v___x_608_;
goto v___jp_641_;
}
}
}
else
{
lean_dec_ref(v_recur_614_);
lean_dec(v___x_608_);
return v_acc_612_;
}
v___jp_615_:
{
if (lean_obj_tag(v_acc_612_) == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v_out_617_);
v___x_619_ = lean_apply_4(v_recur_614_, v_it_616_, v___x_618_, lean_box(0), lean_box(0));
return v___x_619_;
}
else
{
lean_object* v_val_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_631_; 
v_val_620_ = lean_ctor_get(v_acc_612_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v_acc_612_);
if (v_isSharedCheck_631_ == 0)
{
v___x_622_ = v_acc_612_;
v_isShared_623_ = v_isSharedCheck_631_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_val_620_);
lean_dec(v_acc_612_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_631_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_624_ = lean_string_utf8_extract_fast(v___x_604_, v___x_605_, v___x_606_);
v___x_625_ = lean_string_append(v_val_620_, v___x_624_);
lean_dec_ref(v___x_624_);
v___x_626_ = lean_string_append(v___x_625_, v_out_617_);
lean_dec_ref(v_out_617_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_626_);
v___x_628_ = v___x_622_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_630_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; 
v___x_629_ = lean_apply_4(v_recur_614_, v_it_616_, v___x_628_, lean_box(0), lean_box(0));
return v___x_629_;
}
}
}
}
v___jp_632_:
{
if (v___y_636_ == 0)
{
lean_object* v___x_637_; 
v___x_637_ = lean_string_utf8_set(v___y_633_, v___x_605_, v___y_634_);
v_it_616_ = v___y_635_;
v_out_617_ = v___x_637_;
goto v___jp_615_;
}
else
{
uint32_t v___x_638_; uint32_t v___x_639_; lean_object* v___x_640_; 
v___x_638_ = 4294967264;
v___x_639_ = lean_uint32_add(v___y_634_, v___x_638_);
v___x_640_ = lean_string_utf8_set(v___y_633_, v___x_605_, v___x_639_);
v_it_616_ = v___y_635_;
v_out_617_ = v___x_640_;
goto v___jp_615_;
}
}
v___jp_641_:
{
lean_object* v___x_645_; uint32_t v___x_646_; uint32_t v___x_647_; uint8_t v___x_648_; 
v___x_645_ = lean_string_utf8_extract_fast(v_name_607_, v_startInclusive_643_, v_endExclusive_644_);
lean_dec(v_endExclusive_644_);
lean_dec(v_startInclusive_643_);
v___x_646_ = lean_string_utf8_get(v___x_645_, v___x_605_);
v___x_647_ = 97;
v___x_648_ = lean_uint32_dec_le(v___x_647_, v___x_646_);
if (v___x_648_ == 0)
{
v___y_633_ = v___x_645_;
v___y_634_ = v___x_646_;
v___y_635_ = v_it_642_;
v___y_636_ = v___x_648_;
goto v___jp_632_;
}
else
{
uint32_t v___x_649_; uint8_t v___x_650_; 
v___x_649_ = 122;
v___x_650_ = lean_uint32_dec_le(v___x_646_, v___x_649_);
v___y_633_ = v___x_645_;
v___y_634_ = v___x_646_;
v___y_635_ = v_it_642_;
v___y_636_ = v___x_650_;
goto v___jp_632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1___boxed(lean_object* v___x_675_, lean_object* v___x_676_, lean_object* v___x_677_, lean_object* v_name_678_, lean_object* v___x_679_, lean_object* v___x_680_, lean_object* v___x_681_, lean_object* v_it_682_, lean_object* v_acc_683_, lean_object* v_hP_684_, lean_object* v_recur_685_){
_start:
{
uint32_t v___x_3055__boxed_686_; lean_object* v_res_687_; 
v___x_3055__boxed_686_ = lean_unbox_uint32(v___x_680_);
lean_dec(v___x_680_);
v_res_687_ = l_Std_Http_Request_instEncodeV11Head___lam__1(v___x_675_, v___x_676_, v___x_677_, v_name_678_, v___x_679_, v___x_3055__boxed_686_, v___x_681_, v_it_682_, v_acc_683_, v_hP_684_, v_recur_685_);
lean_dec_ref(v___x_681_);
lean_dec_ref(v_name_678_);
lean_dec(v___x_677_);
lean_dec(v___x_676_);
lean_dec_ref(v___x_675_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0(lean_object* v_buf_688_, lean_object* v_name_689_, lean_object* v_value_690_){
_start:
{
lean_object* v___y_692_; lean_object* v___f_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_it_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___f_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___f_711_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__1));
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = lean_string_utf8_byte_size(v_name_689_);
lean_inc_ref(v_name_689_);
v___x_714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_714_, 0, v_name_689_);
lean_ctor_set(v___x_714_, 1, v___x_712_);
lean_ctor_set(v___x_714_, 2, v___x_713_);
lean_inc_ref(v___x_714_);
v_it_715_ = l_String_Slice_splitToSubslice___redArg(v___x_714_, v___f_711_);
v___x_716_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__2));
v___x_717_ = lean_obj_once(&l_Std_Http_Request_instToStringHead___lam__2___closed__3, &l_Std_Http_Request_instToStringHead___lam__2___closed__3_once, _init_l_Std_Http_Request_instToStringHead___lam__2___closed__3);
v___x_718_ = l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1;
v___f_719_ = lean_alloc_closure((void*)(l_Std_Http_Request_instEncodeV11Head___lam__1___boxed), 11, 7);
lean_closure_set(v___f_719_, 0, v___x_716_);
lean_closure_set(v___f_719_, 1, v___x_712_);
lean_closure_set(v___f_719_, 2, v___x_717_);
lean_closure_set(v___f_719_, 3, v_name_689_);
lean_closure_set(v___f_719_, 4, v___x_713_);
lean_closure_set(v___f_719_, 5, v___x_718_);
lean_closure_set(v___f_719_, 6, v___x_714_);
v___x_720_ = lean_box(0);
v___x_721_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_719_, v_it_715_, v___x_720_, lean_box(0));
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v___x_722_; 
v___x_722_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_692_ = v___x_722_;
goto v___jp_691_;
}
else
{
lean_object* v_val_723_; 
v_val_723_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_val_723_);
lean_dec_ref_known(v___x_721_, 1);
v___y_692_ = v_val_723_;
goto v___jp_691_;
}
v___jp_691_:
{
lean_object* v_data_693_; lean_object* v_size_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_710_; 
v_data_693_ = lean_ctor_get(v_buf_688_, 0);
v_size_694_ = lean_ctor_get(v_buf_688_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_buf_688_);
if (v_isSharedCheck_710_ == 0)
{
v___x_696_ = v_buf_688_;
v_isShared_697_ = v_isSharedCheck_710_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_size_694_);
lean_inc(v_data_693_);
lean_dec(v_buf_688_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_710_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_698_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__0));
v___x_699_ = lean_string_append(v___y_692_, v___x_698_);
v___x_700_ = lean_string_append(v___x_699_, v_value_690_);
v___x_701_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__0));
v___x_702_ = lean_string_append(v___x_700_, v___x_701_);
v___x_703_ = lean_string_to_utf8(v___x_702_);
lean_dec_ref(v___x_702_);
lean_inc_ref(v___x_703_);
v___x_704_ = lean_array_push(v_data_693_, v___x_703_);
v___x_705_ = lean_byte_array_size(v___x_703_);
lean_dec_ref(v___x_703_);
v___x_706_ = lean_nat_add(v_size_694_, v___x_705_);
lean_dec(v_size_694_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v___x_706_);
lean_ctor_set(v___x_696_, 0, v___x_704_);
v___x_708_ = v___x_696_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___boxed(lean_object* v_buf_724_, lean_object* v_name_725_, lean_object* v_value_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Std_Http_Request_instEncodeV11Head___lam__0(v_buf_724_, v_name_725_, v_value_726_);
lean_dec_ref(v_value_726_);
return v_res_727_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__0));
v___x_729_ = lean_string_to_utf8(v___x_728_);
return v___x_729_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0);
v___x_731_ = lean_byte_array_size(v___x_730_);
return v___x_731_;
}
}
static uint8_t _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2(void){
_start:
{
uint32_t v___x_732_; uint8_t v___x_733_; 
v___x_732_ = 32;
v___x_733_ = lean_uint32_to_uint8(v___x_732_);
return v___x_733_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3(void){
_start:
{
uint8_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_734_ = lean_uint8_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2);
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = lean_mk_empty_array_with_capacity(v___x_735_);
v___x_737_ = lean_box(v___x_734_);
v___x_738_ = lean_array_push(v___x_736_, v___x_737_);
v___x_739_ = lean_byte_array_mk(v___x_738_);
return v___x_739_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__4(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3);
v___x_741_ = lean_byte_array_size(v___x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3(lean_object* v___f_742_, lean_object* v___f_743_, lean_object* v___f_744_, lean_object* v_buffer_745_, lean_object* v_req_746_){
_start:
{
uint8_t v_method_747_; uint8_t v_version_748_; lean_object* v_uri_749_; lean_object* v_headers_750_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v_port_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v_host_820_; lean_object* v_port_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_904_; lean_object* v_port_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_924_; lean_object* v_host_925_; lean_object* v_port_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_955_; 
v_method_747_ = lean_ctor_get_uint8(v_req_746_, sizeof(void*)*2);
v_version_748_ = lean_ctor_get_uint8(v_req_746_, sizeof(void*)*2 + 1);
v_uri_749_ = lean_ctor_get(v_req_746_, 0);
lean_inc(v_uri_749_);
v_headers_750_ = lean_ctor_get(v_req_746_, 1);
lean_inc_ref(v_headers_750_);
lean_dec_ref(v_req_746_);
switch(v_method_747_)
{
case 0:
{
lean_object* v___x_1035_; 
v___x_1035_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__24));
v___y_955_ = v___x_1035_;
goto v___jp_954_;
}
case 1:
{
lean_object* v___x_1036_; 
v___x_1036_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__25));
v___y_955_ = v___x_1036_;
goto v___jp_954_;
}
case 2:
{
lean_object* v___x_1037_; 
v___x_1037_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__26));
v___y_955_ = v___x_1037_;
goto v___jp_954_;
}
case 3:
{
lean_object* v___x_1038_; 
v___x_1038_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__27));
v___y_955_ = v___x_1038_;
goto v___jp_954_;
}
case 4:
{
lean_object* v___x_1039_; 
v___x_1039_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__28));
v___y_955_ = v___x_1039_;
goto v___jp_954_;
}
case 5:
{
lean_object* v___x_1040_; 
v___x_1040_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__29));
v___y_955_ = v___x_1040_;
goto v___jp_954_;
}
case 6:
{
lean_object* v___x_1041_; 
v___x_1041_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__30));
v___y_955_ = v___x_1041_;
goto v___jp_954_;
}
case 7:
{
lean_object* v___x_1042_; 
v___x_1042_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__31));
v___y_955_ = v___x_1042_;
goto v___jp_954_;
}
case 8:
{
lean_object* v___x_1043_; 
v___x_1043_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__32));
v___y_955_ = v___x_1043_;
goto v___jp_954_;
}
case 9:
{
lean_object* v___x_1044_; 
v___x_1044_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__33));
v___y_955_ = v___x_1044_;
goto v___jp_954_;
}
case 10:
{
lean_object* v___x_1045_; 
v___x_1045_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__34));
v___y_955_ = v___x_1045_;
goto v___jp_954_;
}
case 11:
{
lean_object* v___x_1046_; 
v___x_1046_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__35));
v___y_955_ = v___x_1046_;
goto v___jp_954_;
}
case 12:
{
lean_object* v___x_1047_; 
v___x_1047_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__36));
v___y_955_ = v___x_1047_;
goto v___jp_954_;
}
case 13:
{
lean_object* v___x_1048_; 
v___x_1048_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__37));
v___y_955_ = v___x_1048_;
goto v___jp_954_;
}
case 14:
{
lean_object* v___x_1049_; 
v___x_1049_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__38));
v___y_955_ = v___x_1049_;
goto v___jp_954_;
}
case 15:
{
lean_object* v___x_1050_; 
v___x_1050_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__39));
v___y_955_ = v___x_1050_;
goto v___jp_954_;
}
case 16:
{
lean_object* v___x_1051_; 
v___x_1051_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__40));
v___y_955_ = v___x_1051_;
goto v___jp_954_;
}
case 17:
{
lean_object* v___x_1052_; 
v___x_1052_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__41));
v___y_955_ = v___x_1052_;
goto v___jp_954_;
}
case 18:
{
lean_object* v___x_1053_; 
v___x_1053_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__42));
v___y_955_ = v___x_1053_;
goto v___jp_954_;
}
case 19:
{
lean_object* v___x_1054_; 
v___x_1054_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__43));
v___y_955_ = v___x_1054_;
goto v___jp_954_;
}
case 20:
{
lean_object* v___x_1055_; 
v___x_1055_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__44));
v___y_955_ = v___x_1055_;
goto v___jp_954_;
}
case 21:
{
lean_object* v___x_1056_; 
v___x_1056_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__45));
v___y_955_ = v___x_1056_;
goto v___jp_954_;
}
case 22:
{
lean_object* v___x_1057_; 
v___x_1057_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__46));
v___y_955_ = v___x_1057_;
goto v___jp_954_;
}
case 23:
{
lean_object* v___x_1058_; 
v___x_1058_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__47));
v___y_955_ = v___x_1058_;
goto v___jp_954_;
}
case 24:
{
lean_object* v___x_1059_; 
v___x_1059_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__48));
v___y_955_ = v___x_1059_;
goto v___jp_954_;
}
case 25:
{
lean_object* v___x_1060_; 
v___x_1060_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__49));
v___y_955_ = v___x_1060_;
goto v___jp_954_;
}
case 26:
{
lean_object* v___x_1061_; 
v___x_1061_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__50));
v___y_955_ = v___x_1061_;
goto v___jp_954_;
}
case 27:
{
lean_object* v___x_1062_; 
v___x_1062_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__51));
v___y_955_ = v___x_1062_;
goto v___jp_954_;
}
case 28:
{
lean_object* v___x_1063_; 
v___x_1063_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__52));
v___y_955_ = v___x_1063_;
goto v___jp_954_;
}
case 29:
{
lean_object* v___x_1064_; 
v___x_1064_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__53));
v___y_955_ = v___x_1064_;
goto v___jp_954_;
}
case 30:
{
lean_object* v___x_1065_; 
v___x_1065_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__54));
v___y_955_ = v___x_1065_;
goto v___jp_954_;
}
case 31:
{
lean_object* v___x_1066_; 
v___x_1066_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__55));
v___y_955_ = v___x_1066_;
goto v___jp_954_;
}
case 32:
{
lean_object* v___x_1067_; 
v___x_1067_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__56));
v___y_955_ = v___x_1067_;
goto v___jp_954_;
}
case 33:
{
lean_object* v___x_1068_; 
v___x_1068_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__57));
v___y_955_ = v___x_1068_;
goto v___jp_954_;
}
case 34:
{
lean_object* v___x_1069_; 
v___x_1069_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__58));
v___y_955_ = v___x_1069_;
goto v___jp_954_;
}
case 35:
{
lean_object* v___x_1070_; 
v___x_1070_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__59));
v___y_955_ = v___x_1070_;
goto v___jp_954_;
}
case 36:
{
lean_object* v___x_1071_; 
v___x_1071_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__60));
v___y_955_ = v___x_1071_;
goto v___jp_954_;
}
case 37:
{
lean_object* v___x_1072_; 
v___x_1072_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__61));
v___y_955_ = v___x_1072_;
goto v___jp_954_;
}
case 38:
{
lean_object* v___x_1073_; 
v___x_1073_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__62));
v___y_955_ = v___x_1073_;
goto v___jp_954_;
}
default: 
{
lean_object* v___x_1074_; 
v___x_1074_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__63));
v___y_955_ = v___x_1074_;
goto v___jp_954_;
}
}
v___jp_751_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v_buffer_763_; lean_object* v_buffer_764_; lean_object* v_data_765_; lean_object* v_size_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_775_; 
v___x_755_ = lean_string_to_utf8(v___y_754_);
lean_inc_ref(v___x_755_);
v___x_756_ = lean_array_push(v___y_753_, v___x_755_);
v___x_757_ = lean_byte_array_size(v___x_755_);
lean_dec_ref(v___x_755_);
v___x_758_ = lean_nat_add(v___y_752_, v___x_757_);
lean_dec(v___y_752_);
v___x_759_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0);
v___x_760_ = lean_array_push(v___x_756_, v___x_759_);
v___x_761_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1);
v___x_762_ = lean_nat_add(v___x_758_, v___x_761_);
lean_dec(v___x_758_);
v_buffer_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_763_, 0, v___x_760_);
lean_ctor_set(v_buffer_763_, 1, v___x_762_);
v_buffer_764_ = l_Std_Http_Headers_fold___redArg(v_headers_750_, v_buffer_763_, v___f_742_);
lean_dec_ref(v_headers_750_);
v_data_765_ = lean_ctor_get(v_buffer_764_, 0);
v_size_766_ = lean_ctor_get(v_buffer_764_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v_buffer_764_);
if (v_isSharedCheck_775_ == 0)
{
v___x_768_ = v_buffer_764_;
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_size_766_);
lean_inc(v_data_765_);
lean_dec(v_buffer_764_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_770_ = lean_array_push(v_data_765_, v___x_759_);
v___x_771_ = lean_nat_add(v_size_766_, v___x_761_);
lean_dec(v_size_766_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___x_771_);
lean_ctor_set(v___x_768_, 0, v___x_770_);
v___x_773_ = v___x_768_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
v___jp_776_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_782_ = lean_string_to_utf8(v___y_781_);
lean_dec_ref(v___y_781_);
lean_inc_ref(v___x_782_);
v___x_783_ = lean_array_push(v___y_780_, v___x_782_);
v___x_784_ = lean_byte_array_size(v___x_782_);
lean_dec_ref(v___x_782_);
v___x_785_ = lean_nat_add(v___y_777_, v___x_784_);
lean_dec(v___y_777_);
v___x_786_ = lean_array_push(v___x_783_, v___y_779_);
v___x_787_ = lean_nat_add(v___x_785_, v___y_778_);
lean_dec(v___x_785_);
switch(v_version_748_)
{
case 0:
{
lean_object* v___x_788_; 
v___x_788_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__11));
v___y_752_ = v___x_787_;
v___y_753_ = v___x_786_;
v___y_754_ = v___x_788_;
goto v___jp_751_;
}
case 1:
{
lean_object* v___x_789_; 
v___x_789_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__12));
v___y_752_ = v___x_787_;
v___y_753_ = v___x_786_;
v___y_754_ = v___x_789_;
goto v___jp_751_;
}
case 2:
{
lean_object* v___x_790_; 
v___x_790_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__13));
v___y_752_ = v___x_787_;
v___y_753_ = v___x_786_;
v___y_754_ = v___x_790_;
goto v___jp_751_;
}
default: 
{
lean_object* v___x_791_; 
v___x_791_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__14));
v___y_752_ = v___x_787_;
v___y_753_ = v___x_786_;
v___y_754_ = v___x_791_;
goto v___jp_751_;
}
}
}
v___jp_792_:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_string_append(v___y_794_, v___y_796_);
lean_dec_ref(v___y_796_);
v___x_801_ = lean_string_append(v___x_800_, v___y_799_);
lean_dec_ref(v___y_799_);
v___y_777_ = v___y_793_;
v___y_778_ = v___y_795_;
v___y_779_ = v___y_797_;
v___y_780_ = v___y_798_;
v___y_781_ = v___x_801_;
goto v___jp_776_;
}
v___jp_802_:
{
switch(lean_obj_tag(v_port_805_))
{
case 0:
{
lean_object* v___x_810_; 
v___x_810_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_793_ = v___y_803_;
v___y_794_ = v___y_804_;
v___y_795_ = v___y_806_;
v___y_796_ = v___y_809_;
v___y_797_ = v___y_807_;
v___y_798_ = v___y_808_;
v___y_799_ = v___x_810_;
goto v___jp_792_;
}
case 1:
{
lean_object* v___x_811_; 
v___x_811_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_793_ = v___y_803_;
v___y_794_ = v___y_804_;
v___y_795_ = v___y_806_;
v___y_796_ = v___y_809_;
v___y_797_ = v___y_807_;
v___y_798_ = v___y_808_;
v___y_799_ = v___x_811_;
goto v___jp_792_;
}
default: 
{
uint16_t v_port_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_port_812_ = lean_ctor_get_uint16(v_port_805_, 0);
lean_dec_ref_known(v_port_805_, 0);
v___x_813_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_814_ = lean_uint16_to_nat(v_port_812_);
v___x_815_ = l_Nat_reprFast(v___x_814_);
v___x_816_ = lean_string_append(v___x_813_, v___x_815_);
lean_dec_ref(v___x_815_);
v___y_793_ = v___y_803_;
v___y_794_ = v___y_804_;
v___y_795_ = v___y_806_;
v___y_796_ = v___y_809_;
v___y_797_ = v___y_807_;
v___y_798_ = v___y_808_;
v___y_799_ = v___x_816_;
goto v___jp_792_;
}
}
}
v___jp_817_:
{
switch(lean_obj_tag(v_host_820_))
{
case 0:
{
lean_object* v_name_825_; 
v_name_825_ = lean_ctor_get(v_host_820_, 0);
lean_inc_ref(v_name_825_);
lean_dec_ref_known(v_host_820_, 1);
v___y_803_ = v___y_818_;
v___y_804_ = v___y_824_;
v_port_805_ = v_port_821_;
v___y_806_ = v___y_819_;
v___y_807_ = v___y_822_;
v___y_808_ = v___y_823_;
v___y_809_ = v_name_825_;
goto v___jp_802_;
}
case 1:
{
lean_object* v_ipv4_826_; lean_object* v___x_827_; 
v_ipv4_826_ = lean_ctor_get(v_host_820_, 0);
lean_inc_ref(v_ipv4_826_);
lean_dec_ref_known(v_host_820_, 1);
v___x_827_ = lean_uv_ntop_v4(v_ipv4_826_);
lean_dec_ref(v_ipv4_826_);
v___y_803_ = v___y_818_;
v___y_804_ = v___y_824_;
v_port_805_ = v_port_821_;
v___y_806_ = v___y_819_;
v___y_807_ = v___y_822_;
v___y_808_ = v___y_823_;
v___y_809_ = v___x_827_;
goto v___jp_802_;
}
default: 
{
lean_object* v_ipv6_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_ipv6_828_ = lean_ctor_get(v_host_820_, 0);
lean_inc_ref(v_ipv6_828_);
lean_dec_ref_known(v_host_820_, 1);
v___x_829_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_830_ = lean_uv_ntop_v6(v_ipv6_828_);
lean_dec_ref(v_ipv6_828_);
v___x_831_ = lean_string_append(v___x_829_, v___x_830_);
lean_dec_ref(v___x_830_);
v___x_832_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_833_ = lean_string_append(v___x_831_, v___x_832_);
v___y_803_ = v___y_818_;
v___y_804_ = v___y_824_;
v_port_805_ = v_port_821_;
v___y_806_ = v___y_819_;
v___y_807_ = v___y_822_;
v___y_808_ = v___y_823_;
v___y_809_ = v___x_833_;
goto v___jp_802_;
}
}
}
v___jp_834_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_844_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_845_ = lean_string_append(v___y_841_, v___x_844_);
v___x_846_ = lean_string_append(v___x_845_, v___y_839_);
lean_dec_ref(v___y_839_);
v___x_847_ = lean_string_append(v___x_846_, v___y_838_);
lean_dec_ref(v___y_838_);
v___x_848_ = lean_string_append(v___x_847_, v___y_837_);
lean_dec_ref(v___y_837_);
v___x_849_ = lean_string_append(v___x_848_, v___y_843_);
lean_dec_ref(v___y_843_);
v___y_777_ = v___y_835_;
v___y_778_ = v___y_836_;
v___y_779_ = v___y_840_;
v___y_780_ = v___y_842_;
v___y_781_ = v___x_849_;
goto v___jp_776_;
}
v___jp_850_:
{
lean_object* v_queryPart_860_; 
v_queryPart_860_ = l_Std_Http_URI_Query_formatOption(v___y_854_);
if (lean_obj_tag(v___y_858_) == 0)
{
lean_object* v___x_861_; 
v___x_861_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_835_ = v___y_851_;
v___y_836_ = v___y_852_;
v___y_837_ = v_queryPart_860_;
v___y_838_ = v___y_859_;
v___y_839_ = v___y_853_;
v___y_840_ = v___y_856_;
v___y_841_ = v___y_855_;
v___y_842_ = v___y_857_;
v___y_843_ = v___x_861_;
goto v___jp_834_;
}
else
{
lean_object* v_val_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_val_862_ = lean_ctor_get(v___y_858_, 0);
lean_inc(v_val_862_);
lean_dec_ref_known(v___y_858_, 1);
v___x_863_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__16));
v___x_864_ = l_Std_Http_URI_EncodedFragment_encode(v_val_862_);
lean_dec(v_val_862_);
v___x_865_ = lean_string_from_utf8_unchecked(v___x_864_);
v___x_866_ = lean_string_append(v___x_863_, v___x_865_);
lean_dec_ref(v___x_865_);
v___y_835_ = v___y_851_;
v___y_836_ = v___y_852_;
v___y_837_ = v_queryPart_860_;
v___y_838_ = v___y_859_;
v___y_839_ = v___y_853_;
v___y_840_ = v___y_856_;
v___y_841_ = v___y_855_;
v___y_842_ = v___y_857_;
v___y_843_ = v___x_866_;
goto v___jp_834_;
}
}
v___jp_867_:
{
lean_object* v_segments_877_; uint8_t v_absolute_878_; lean_object* v___x_879_; lean_object* v___x_880_; size_t v_sz_881_; size_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v_result_885_; 
v_segments_877_ = lean_ctor_get(v___y_874_, 0);
lean_inc_ref(v_segments_877_);
v_absolute_878_ = lean_ctor_get_uint8(v___y_874_, sizeof(void*)*1);
lean_dec_ref(v___y_874_);
v___x_879_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_880_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_881_ = lean_array_size(v_segments_877_);
v___x_882_ = ((size_t)0ULL);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_880_, v___f_743_, v_sz_881_, v___x_882_, v_segments_877_);
v___x_884_ = lean_array_to_list(v___x_883_);
v_result_885_ = l_String_intercalate(v___x_879_, v___x_884_);
if (v_absolute_878_ == 0)
{
v___y_851_ = v___y_868_;
v___y_852_ = v___y_869_;
v___y_853_ = v___y_876_;
v___y_854_ = v___y_870_;
v___y_855_ = v___y_872_;
v___y_856_ = v___y_871_;
v___y_857_ = v___y_873_;
v___y_858_ = v___y_875_;
v___y_859_ = v_result_885_;
goto v___jp_850_;
}
else
{
lean_object* v___x_886_; 
v___x_886_ = lean_string_append(v___x_879_, v_result_885_);
lean_dec_ref(v_result_885_);
v___y_851_ = v___y_868_;
v___y_852_ = v___y_869_;
v___y_853_ = v___y_876_;
v___y_854_ = v___y_870_;
v___y_855_ = v___y_872_;
v___y_856_ = v___y_871_;
v___y_857_ = v___y_873_;
v___y_858_ = v___y_875_;
v___y_859_ = v___x_886_;
goto v___jp_850_;
}
}
v___jp_887_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_900_ = lean_string_append(v___y_891_, v___y_888_);
lean_dec_ref(v___y_888_);
v___x_901_ = lean_string_append(v___x_900_, v___y_899_);
lean_dec_ref(v___y_899_);
lean_inc_ref(v___y_893_);
v___x_902_ = lean_string_append(v___y_893_, v___x_901_);
lean_dec_ref(v___x_901_);
v___y_868_ = v___y_889_;
v___y_869_ = v___y_890_;
v___y_870_ = v___y_892_;
v___y_871_ = v___y_895_;
v___y_872_ = v___y_894_;
v___y_873_ = v___y_896_;
v___y_874_ = v___y_898_;
v___y_875_ = v___y_897_;
v___y_876_ = v___x_902_;
goto v___jp_867_;
}
v___jp_903_:
{
switch(lean_obj_tag(v_port_905_))
{
case 0:
{
lean_object* v___x_916_; 
v___x_916_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_888_ = v___y_915_;
v___y_889_ = v___y_904_;
v___y_890_ = v___y_907_;
v___y_891_ = v___y_906_;
v___y_892_ = v___y_908_;
v___y_893_ = v___y_909_;
v___y_894_ = v___y_911_;
v___y_895_ = v___y_910_;
v___y_896_ = v___y_912_;
v___y_897_ = v___y_914_;
v___y_898_ = v___y_913_;
v___y_899_ = v___x_916_;
goto v___jp_887_;
}
case 1:
{
lean_object* v___x_917_; 
v___x_917_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_888_ = v___y_915_;
v___y_889_ = v___y_904_;
v___y_890_ = v___y_907_;
v___y_891_ = v___y_906_;
v___y_892_ = v___y_908_;
v___y_893_ = v___y_909_;
v___y_894_ = v___y_911_;
v___y_895_ = v___y_910_;
v___y_896_ = v___y_912_;
v___y_897_ = v___y_914_;
v___y_898_ = v___y_913_;
v___y_899_ = v___x_917_;
goto v___jp_887_;
}
default: 
{
uint16_t v_port_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_port_918_ = lean_ctor_get_uint16(v_port_905_, 0);
lean_dec_ref_known(v_port_905_, 0);
v___x_919_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_920_ = lean_uint16_to_nat(v_port_918_);
v___x_921_ = l_Nat_reprFast(v___x_920_);
v___x_922_ = lean_string_append(v___x_919_, v___x_921_);
lean_dec_ref(v___x_921_);
v___y_888_ = v___y_915_;
v___y_889_ = v___y_904_;
v___y_890_ = v___y_907_;
v___y_891_ = v___y_906_;
v___y_892_ = v___y_908_;
v___y_893_ = v___y_909_;
v___y_894_ = v___y_911_;
v___y_895_ = v___y_910_;
v___y_896_ = v___y_912_;
v___y_897_ = v___y_914_;
v___y_898_ = v___y_913_;
v___y_899_ = v___x_922_;
goto v___jp_887_;
}
}
}
v___jp_923_:
{
switch(lean_obj_tag(v_host_925_))
{
case 0:
{
lean_object* v_name_936_; 
v_name_936_ = lean_ctor_get(v_host_925_, 0);
lean_inc_ref(v_name_936_);
lean_dec_ref_known(v_host_925_, 1);
v___y_904_ = v___y_924_;
v_port_905_ = v_port_926_;
v___y_906_ = v___y_935_;
v___y_907_ = v___y_927_;
v___y_908_ = v___y_928_;
v___y_909_ = v___y_929_;
v___y_910_ = v___y_931_;
v___y_911_ = v___y_930_;
v___y_912_ = v___y_932_;
v___y_913_ = v___y_934_;
v___y_914_ = v___y_933_;
v___y_915_ = v_name_936_;
goto v___jp_903_;
}
case 1:
{
lean_object* v_ipv4_937_; lean_object* v___x_938_; 
v_ipv4_937_ = lean_ctor_get(v_host_925_, 0);
lean_inc_ref(v_ipv4_937_);
lean_dec_ref_known(v_host_925_, 1);
v___x_938_ = lean_uv_ntop_v4(v_ipv4_937_);
lean_dec_ref(v_ipv4_937_);
v___y_904_ = v___y_924_;
v_port_905_ = v_port_926_;
v___y_906_ = v___y_935_;
v___y_907_ = v___y_927_;
v___y_908_ = v___y_928_;
v___y_909_ = v___y_929_;
v___y_910_ = v___y_931_;
v___y_911_ = v___y_930_;
v___y_912_ = v___y_932_;
v___y_913_ = v___y_934_;
v___y_914_ = v___y_933_;
v___y_915_ = v___x_938_;
goto v___jp_903_;
}
default: 
{
lean_object* v_ipv6_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_ipv6_939_ = lean_ctor_get(v_host_925_, 0);
lean_inc_ref(v_ipv6_939_);
lean_dec_ref_known(v_host_925_, 1);
v___x_940_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_941_ = lean_uv_ntop_v6(v_ipv6_939_);
lean_dec_ref(v_ipv6_939_);
v___x_942_ = lean_string_append(v___x_940_, v___x_941_);
lean_dec_ref(v___x_941_);
v___x_943_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_944_ = lean_string_append(v___x_942_, v___x_943_);
v___y_904_ = v___y_924_;
v_port_905_ = v_port_926_;
v___y_906_ = v___y_935_;
v___y_907_ = v___y_927_;
v___y_908_ = v___y_928_;
v___y_909_ = v___y_929_;
v___y_910_ = v___y_931_;
v___y_911_ = v___y_930_;
v___y_912_ = v___y_932_;
v___y_913_ = v___y_934_;
v___y_914_ = v___y_933_;
v___y_915_ = v___x_944_;
goto v___jp_903_;
}
}
}
v___jp_945_:
{
lean_object* v_queryStr_952_; lean_object* v___x_953_; 
v_queryStr_952_ = l_Std_Http_URI_Query_formatOption(v___y_947_);
v___x_953_ = lean_string_append(v___y_951_, v_queryStr_952_);
lean_dec_ref(v_queryStr_952_);
v___y_777_ = v___y_946_;
v___y_778_ = v___y_948_;
v___y_779_ = v___y_949_;
v___y_780_ = v___y_950_;
v___y_781_ = v___x_953_;
goto v___jp_776_;
}
v___jp_954_:
{
lean_object* v_data_956_; lean_object* v_size_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_data_956_ = lean_ctor_get(v_buffer_745_, 0);
lean_inc_ref(v_data_956_);
v_size_957_ = lean_ctor_get(v_buffer_745_, 1);
lean_inc(v_size_957_);
lean_dec_ref(v_buffer_745_);
v___x_958_ = lean_string_to_utf8(v___y_955_);
lean_inc_ref(v___x_958_);
v___x_959_ = lean_array_push(v_data_956_, v___x_958_);
v___x_960_ = lean_byte_array_size(v___x_958_);
lean_dec_ref(v___x_958_);
v___x_961_ = lean_nat_add(v_size_957_, v___x_960_);
lean_dec(v_size_957_);
v___x_962_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3);
v___x_963_ = lean_array_push(v___x_959_, v___x_962_);
v___x_964_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__4, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__4_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__4);
v___x_965_ = lean_nat_add(v___x_961_, v___x_964_);
lean_dec(v___x_961_);
switch(lean_obj_tag(v_uri_749_))
{
case 0:
{
lean_object* v_path_966_; lean_object* v_query_967_; lean_object* v_segments_968_; uint8_t v_absolute_969_; lean_object* v___x_970_; lean_object* v___x_971_; size_t v_sz_972_; size_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v_result_976_; 
lean_dec_ref(v___f_743_);
v_path_966_ = lean_ctor_get(v_uri_749_, 0);
lean_inc_ref(v_path_966_);
v_query_967_ = lean_ctor_get(v_uri_749_, 1);
lean_inc(v_query_967_);
lean_dec_ref_known(v_uri_749_, 2);
v_segments_968_ = lean_ctor_get(v_path_966_, 0);
lean_inc_ref(v_segments_968_);
v_absolute_969_ = lean_ctor_get_uint8(v_path_966_, sizeof(void*)*1);
lean_dec_ref(v_path_966_);
v___x_970_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_971_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_972_ = lean_array_size(v_segments_968_);
v___x_973_ = ((size_t)0ULL);
v___x_974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_971_, v___f_744_, v_sz_972_, v___x_973_, v_segments_968_);
v___x_975_ = lean_array_to_list(v___x_974_);
v_result_976_ = l_String_intercalate(v___x_970_, v___x_975_);
if (v_absolute_969_ == 0)
{
v___y_946_ = v___x_965_;
v___y_947_ = v_query_967_;
v___y_948_ = v___x_964_;
v___y_949_ = v___x_962_;
v___y_950_ = v___x_963_;
v___y_951_ = v_result_976_;
goto v___jp_945_;
}
else
{
lean_object* v___x_977_; 
v___x_977_ = lean_string_append(v___x_970_, v_result_976_);
lean_dec_ref(v_result_976_);
v___y_946_ = v___x_965_;
v___y_947_ = v_query_967_;
v___y_948_ = v___x_964_;
v___y_949_ = v___x_962_;
v___y_950_ = v___x_963_;
v___y_951_ = v___x_977_;
goto v___jp_945_;
}
}
case 1:
{
lean_object* v_uri_978_; lean_object* v_authority_979_; 
lean_dec_ref(v___f_744_);
v_uri_978_ = lean_ctor_get(v_uri_749_, 0);
lean_inc_ref(v_uri_978_);
lean_dec_ref_known(v_uri_749_, 1);
v_authority_979_ = lean_ctor_get(v_uri_978_, 1);
if (lean_obj_tag(v_authority_979_) == 0)
{
lean_object* v_scheme_980_; lean_object* v_path_981_; lean_object* v_query_982_; lean_object* v_fragment_983_; lean_object* v___x_984_; 
v_scheme_980_ = lean_ctor_get(v_uri_978_, 0);
lean_inc_ref(v_scheme_980_);
v_path_981_ = lean_ctor_get(v_uri_978_, 2);
lean_inc_ref(v_path_981_);
v_query_982_ = lean_ctor_get(v_uri_978_, 3);
lean_inc(v_query_982_);
v_fragment_983_ = lean_ctor_get(v_uri_978_, 4);
lean_inc(v_fragment_983_);
lean_dec_ref(v_uri_978_);
v___x_984_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_868_ = v___x_965_;
v___y_869_ = v___x_964_;
v___y_870_ = v_query_982_;
v___y_871_ = v___x_962_;
v___y_872_ = v_scheme_980_;
v___y_873_ = v___x_963_;
v___y_874_ = v_path_981_;
v___y_875_ = v_fragment_983_;
v___y_876_ = v___x_984_;
goto v___jp_867_;
}
else
{
lean_object* v_val_985_; lean_object* v_scheme_986_; lean_object* v_path_987_; lean_object* v_query_988_; lean_object* v_fragment_989_; lean_object* v_userInfo_990_; lean_object* v_host_991_; lean_object* v_port_992_; lean_object* v___x_993_; 
v_val_985_ = lean_ctor_get(v_authority_979_, 0);
lean_inc(v_val_985_);
v_scheme_986_ = lean_ctor_get(v_uri_978_, 0);
lean_inc_ref(v_scheme_986_);
v_path_987_ = lean_ctor_get(v_uri_978_, 2);
lean_inc_ref(v_path_987_);
v_query_988_ = lean_ctor_get(v_uri_978_, 3);
lean_inc(v_query_988_);
v_fragment_989_ = lean_ctor_get(v_uri_978_, 4);
lean_inc(v_fragment_989_);
lean_dec_ref(v_uri_978_);
v_userInfo_990_ = lean_ctor_get(v_val_985_, 0);
lean_inc(v_userInfo_990_);
v_host_991_ = lean_ctor_get(v_val_985_, 1);
lean_inc_ref(v_host_991_);
v_port_992_ = lean_ctor_get(v_val_985_, 2);
lean_inc(v_port_992_);
lean_dec(v_val_985_);
v___x_993_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__21));
if (lean_obj_tag(v_userInfo_990_) == 0)
{
lean_object* v___x_994_; 
v___x_994_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_924_ = v___x_965_;
v_host_925_ = v_host_991_;
v_port_926_ = v_port_992_;
v___y_927_ = v___x_964_;
v___y_928_ = v_query_988_;
v___y_929_ = v___x_993_;
v___y_930_ = v_scheme_986_;
v___y_931_ = v___x_962_;
v___y_932_ = v___x_963_;
v___y_933_ = v_fragment_989_;
v___y_934_ = v_path_987_;
v___y_935_ = v___x_994_;
goto v___jp_923_;
}
else
{
lean_object* v_val_995_; lean_object* v_password_996_; 
v_val_995_ = lean_ctor_get(v_userInfo_990_, 0);
lean_inc(v_val_995_);
lean_dec_ref_known(v_userInfo_990_, 1);
v_password_996_ = lean_ctor_get(v_val_995_, 1);
if (lean_obj_tag(v_password_996_) == 0)
{
lean_object* v_username_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v_username_997_ = lean_ctor_get(v_val_995_, 0);
lean_inc_ref(v_username_997_);
lean_dec(v_val_995_);
v___x_998_ = lean_string_from_utf8_unchecked(v_username_997_);
v___x_999_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_1000_ = lean_string_append(v___x_998_, v___x_999_);
v___y_924_ = v___x_965_;
v_host_925_ = v_host_991_;
v_port_926_ = v_port_992_;
v___y_927_ = v___x_964_;
v___y_928_ = v_query_988_;
v___y_929_ = v___x_993_;
v___y_930_ = v_scheme_986_;
v___y_931_ = v___x_962_;
v___y_932_ = v___x_963_;
v___y_933_ = v_fragment_989_;
v___y_934_ = v_path_987_;
v___y_935_ = v___x_1000_;
goto v___jp_923_;
}
else
{
lean_object* v_username_1001_; lean_object* v_val_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_inc_ref(v_password_996_);
v_username_1001_ = lean_ctor_get(v_val_995_, 0);
lean_inc_ref(v_username_1001_);
lean_dec(v_val_995_);
v_val_1002_ = lean_ctor_get(v_password_996_, 0);
lean_inc(v_val_1002_);
lean_dec_ref_known(v_password_996_, 1);
v___x_1003_ = lean_string_from_utf8_unchecked(v_username_1001_);
v___x_1004_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_1005_ = lean_string_append(v___x_1003_, v___x_1004_);
v___x_1006_ = lean_string_from_utf8_unchecked(v_val_1002_);
v___x_1007_ = lean_string_append(v___x_1005_, v___x_1006_);
lean_dec_ref(v___x_1006_);
v___x_1008_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_1009_ = lean_string_append(v___x_1007_, v___x_1008_);
v___y_924_ = v___x_965_;
v_host_925_ = v_host_991_;
v_port_926_ = v_port_992_;
v___y_927_ = v___x_964_;
v___y_928_ = v_query_988_;
v___y_929_ = v___x_993_;
v___y_930_ = v_scheme_986_;
v___y_931_ = v___x_962_;
v___y_932_ = v___x_963_;
v___y_933_ = v_fragment_989_;
v___y_934_ = v_path_987_;
v___y_935_ = v___x_1009_;
goto v___jp_923_;
}
}
}
}
case 2:
{
lean_object* v_authority_1010_; lean_object* v_userInfo_1011_; 
lean_dec_ref(v___f_744_);
lean_dec_ref(v___f_743_);
v_authority_1010_ = lean_ctor_get(v_uri_749_, 0);
lean_inc_ref(v_authority_1010_);
lean_dec_ref_known(v_uri_749_, 1);
v_userInfo_1011_ = lean_ctor_get(v_authority_1010_, 0);
if (lean_obj_tag(v_userInfo_1011_) == 0)
{
lean_object* v_host_1012_; lean_object* v_port_1013_; lean_object* v___x_1014_; 
v_host_1012_ = lean_ctor_get(v_authority_1010_, 1);
lean_inc_ref(v_host_1012_);
v_port_1013_ = lean_ctor_get(v_authority_1010_, 2);
lean_inc(v_port_1013_);
lean_dec_ref(v_authority_1010_);
v___x_1014_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__4));
v___y_818_ = v___x_965_;
v___y_819_ = v___x_964_;
v_host_820_ = v_host_1012_;
v_port_821_ = v_port_1013_;
v___y_822_ = v___x_962_;
v___y_823_ = v___x_963_;
v___y_824_ = v___x_1014_;
goto v___jp_817_;
}
else
{
lean_object* v_val_1015_; lean_object* v_password_1016_; 
v_val_1015_ = lean_ctor_get(v_userInfo_1011_, 0);
lean_inc(v_val_1015_);
v_password_1016_ = lean_ctor_get(v_val_1015_, 1);
if (lean_obj_tag(v_password_1016_) == 0)
{
lean_object* v_host_1017_; lean_object* v_port_1018_; lean_object* v_username_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_host_1017_ = lean_ctor_get(v_authority_1010_, 1);
lean_inc_ref(v_host_1017_);
v_port_1018_ = lean_ctor_get(v_authority_1010_, 2);
lean_inc(v_port_1018_);
lean_dec_ref(v_authority_1010_);
v_username_1019_ = lean_ctor_get(v_val_1015_, 0);
lean_inc_ref(v_username_1019_);
lean_dec(v_val_1015_);
v___x_1020_ = lean_string_from_utf8_unchecked(v_username_1019_);
v___x_1021_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_1022_ = lean_string_append(v___x_1020_, v___x_1021_);
v___y_818_ = v___x_965_;
v___y_819_ = v___x_964_;
v_host_820_ = v_host_1017_;
v_port_821_ = v_port_1018_;
v___y_822_ = v___x_962_;
v___y_823_ = v___x_963_;
v___y_824_ = v___x_1022_;
goto v___jp_817_;
}
else
{
lean_object* v_host_1023_; lean_object* v_port_1024_; lean_object* v_username_1025_; lean_object* v_val_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_inc_ref(v_password_1016_);
v_host_1023_ = lean_ctor_get(v_authority_1010_, 1);
lean_inc_ref(v_host_1023_);
v_port_1024_ = lean_ctor_get(v_authority_1010_, 2);
lean_inc(v_port_1024_);
lean_dec_ref(v_authority_1010_);
v_username_1025_ = lean_ctor_get(v_val_1015_, 0);
lean_inc_ref(v_username_1025_);
lean_dec(v_val_1015_);
v_val_1026_ = lean_ctor_get(v_password_1016_, 0);
lean_inc(v_val_1026_);
lean_dec_ref_known(v_password_1016_, 1);
v___x_1027_ = lean_string_from_utf8_unchecked(v_username_1025_);
v___x_1028_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_1029_ = lean_string_append(v___x_1027_, v___x_1028_);
v___x_1030_ = lean_string_from_utf8_unchecked(v_val_1026_);
v___x_1031_ = lean_string_append(v___x_1029_, v___x_1030_);
lean_dec_ref(v___x_1030_);
v___x_1032_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_1033_ = lean_string_append(v___x_1031_, v___x_1032_);
v___y_818_ = v___x_965_;
v___y_819_ = v___x_964_;
v_host_820_ = v_host_1023_;
v_port_821_ = v_port_1024_;
v___y_822_ = v___x_962_;
v___y_823_ = v___x_963_;
v___y_824_ = v___x_1033_;
goto v___jp_817_;
}
}
}
default: 
{
lean_object* v___x_1034_; 
lean_dec_ref(v___f_744_);
lean_dec_ref(v___f_743_);
v___x_1034_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__23));
v___y_777_ = v___x_965_;
v___y_778_ = v___x_964_;
v___y_779_ = v___x_962_;
v___y_780_ = v___x_963_;
v___y_781_ = v___x_1034_;
goto v___jp_776_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__0(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; 
v___x_1080_ = l_Std_Http_Headers_empty;
v___x_1081_ = lean_box(3);
v___x_1082_ = 1;
v___x_1083_ = 8;
v___x_1084_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1084_, 0, v___x_1081_);
lean_ctor_set(v___x_1084_, 1, v___x_1080_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*2, v___x_1083_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*2 + 1, v___x_1082_);
return v___x_1084_;
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__1(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = l_Std_Http_Extensions_empty;
v___x_1086_ = lean_obj_once(&l_Std_Http_Request_new___closed__0, &l_Std_Http_Request_new___closed__0_once, _init_l_Std_Http_Request_new___closed__0);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v___x_1085_);
return v___x_1087_;
}
}
static lean_object* _init_l_Std_Http_Request_new(void){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_obj_once(&l_Std_Http_Request_new___closed__1, &l_Std_Http_Request_new___closed__1_once, _init_l_Std_Http_Request_new___closed__1);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method(lean_object* v_builder_1089_, uint8_t v_method_1090_){
_start:
{
lean_object* v_line_1091_; lean_object* v_extensions_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1109_; 
v_line_1091_ = lean_ctor_get(v_builder_1089_, 0);
v_extensions_1092_ = lean_ctor_get(v_builder_1089_, 1);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_builder_1089_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1094_ = v_builder_1089_;
v_isShared_1095_ = v_isSharedCheck_1109_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_extensions_1092_);
lean_inc(v_line_1091_);
lean_dec(v_builder_1089_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1109_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
uint8_t v_version_1096_; lean_object* v_uri_1097_; lean_object* v_headers_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1108_; 
v_version_1096_ = lean_ctor_get_uint8(v_line_1091_, sizeof(void*)*2 + 1);
v_uri_1097_ = lean_ctor_get(v_line_1091_, 0);
v_headers_1098_ = lean_ctor_get(v_line_1091_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_line_1091_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1100_ = v_line_1091_;
v_isShared_1101_ = v_isSharedCheck_1108_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_headers_1098_);
lean_inc(v_uri_1097_);
lean_dec(v_line_1091_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1108_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_uri_1097_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_headers_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1107_, sizeof(void*)*2 + 1, v_version_1096_);
v___x_1103_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1105_; 
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*2, v_method_1090_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1103_);
v___x_1105_ = v___x_1094_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_extensions_1092_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method___boxed(lean_object* v_builder_1110_, lean_object* v_method_1111_){
_start:
{
uint8_t v_method_boxed_1112_; lean_object* v_res_1113_; 
v_method_boxed_1112_ = lean_unbox(v_method_1111_);
v_res_1113_ = l_Std_Http_Request_Builder_method(v_builder_1110_, v_method_boxed_1112_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version(lean_object* v_builder_1114_, uint8_t v_version_1115_){
_start:
{
lean_object* v_line_1116_; lean_object* v_extensions_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1134_; 
v_line_1116_ = lean_ctor_get(v_builder_1114_, 0);
v_extensions_1117_ = lean_ctor_get(v_builder_1114_, 1);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_builder_1114_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1119_ = v_builder_1114_;
v_isShared_1120_ = v_isSharedCheck_1134_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_extensions_1117_);
lean_inc(v_line_1116_);
lean_dec(v_builder_1114_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1134_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
uint8_t v_method_1121_; lean_object* v_uri_1122_; lean_object* v_headers_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1133_; 
v_method_1121_ = lean_ctor_get_uint8(v_line_1116_, sizeof(void*)*2);
v_uri_1122_ = lean_ctor_get(v_line_1116_, 0);
v_headers_1123_ = lean_ctor_get(v_line_1116_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_line_1116_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1125_ = v_line_1116_;
v_isShared_1126_ = v_isSharedCheck_1133_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_headers_1123_);
lean_inc(v_uri_1122_);
lean_dec(v_line_1116_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1133_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_uri_1122_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_headers_1123_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, sizeof(void*)*2, v_method_1121_);
v___x_1128_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v___x_1130_; 
lean_ctor_set_uint8(v___x_1128_, sizeof(void*)*2 + 1, v_version_1115_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___x_1128_);
v___x_1130_ = v___x_1119_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_extensions_1117_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version___boxed(lean_object* v_builder_1135_, lean_object* v_version_1136_){
_start:
{
uint8_t v_version_boxed_1137_; lean_object* v_res_1138_; 
v_version_boxed_1137_ = lean_unbox(v_version_1136_);
v_res_1138_ = l_Std_Http_Request_Builder_version(v_builder_1135_, v_version_boxed_1137_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri(lean_object* v_builder_1139_, lean_object* v_uri_1140_){
_start:
{
lean_object* v_line_1141_; lean_object* v_extensions_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1160_; 
v_line_1141_ = lean_ctor_get(v_builder_1139_, 0);
v_extensions_1142_ = lean_ctor_get(v_builder_1139_, 1);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_builder_1139_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1144_ = v_builder_1139_;
v_isShared_1145_ = v_isSharedCheck_1160_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_extensions_1142_);
lean_inc(v_line_1141_);
lean_dec(v_builder_1139_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1160_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
uint8_t v_method_1146_; uint8_t v_version_1147_; lean_object* v_headers_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1158_; 
v_method_1146_ = lean_ctor_get_uint8(v_line_1141_, sizeof(void*)*2);
v_version_1147_ = lean_ctor_get_uint8(v_line_1141_, sizeof(void*)*2 + 1);
v_headers_1148_ = lean_ctor_get(v_line_1141_, 1);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_line_1141_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; 
v_unused_1159_ = lean_ctor_get(v_line_1141_, 0);
lean_dec(v_unused_1159_);
v___x_1150_ = v_line_1141_;
v_isShared_1151_ = v_isSharedCheck_1158_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_headers_1148_);
lean_dec(v_line_1141_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1158_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_uri_1140_);
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_uri_1140_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_headers_1148_);
lean_ctor_set_uint8(v_reuseFailAlloc_1157_, sizeof(void*)*2, v_method_1146_);
lean_ctor_set_uint8(v_reuseFailAlloc_1157_, sizeof(void*)*2 + 1, v_version_1147_);
v___x_1153_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1155_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1153_);
v___x_1155_ = v___x_1144_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_extensions_1142_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(lean_object* v_msg_1161_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = l_Std_Http_instInhabitedRequestTarget_default;
v___x_1163_ = lean_panic_fn_borrowed(v___x_1162_, v_msg_1161_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___lam__0(lean_object* v___x_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_pos_1170_; lean_object* v_array_1171_; lean_object* v_idx_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v_pos_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_pos_1170_);
v_array_1171_ = lean_ctor_get(v_pos_1170_, 0);
v_idx_1172_ = lean_ctor_get(v_pos_1170_, 1);
v___x_1173_ = lean_byte_array_size(v_array_1171_);
v___x_1174_ = lean_nat_dec_lt(v_idx_1172_, v___x_1173_);
if (v___x_1174_ == 0)
{
lean_dec(v_pos_1170_);
return v___x_1169_;
}
else
{
lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1182_; 
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; lean_object* v_unused_1184_; 
v_unused_1183_ = lean_ctor_get(v___x_1169_, 1);
lean_dec(v_unused_1183_);
v_unused_1184_ = lean_ctor_get(v___x_1169_, 0);
lean_dec(v_unused_1184_);
v___x_1176_ = v___x_1169_;
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
else
{
lean_dec(v___x_1169_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___lam__0___closed__1));
if (v_isShared_1177_ == 0)
{
lean_ctor_set_tag(v___x_1176_, 1);
lean_ctor_set(v___x_1176_, 1, v___x_1178_);
v___x_1180_ = v___x_1176_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_pos_1170_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
else
{
return v___x_1169_;
}
}
}
static lean_object* _init_l_Std_Http_Request_Builder_uri_x21___closed__5(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1198_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__4));
v___x_1199_ = lean_unsigned_to_nat(12u);
v___x_1200_ = lean_unsigned_to_nat(45u);
v___x_1201_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__3));
v___x_1202_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__2));
v___x_1203_ = l_mkPanicMessageWithDecl(v___x_1202_, v___x_1201_, v___x_1200_, v___x_1199_, v___x_1198_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21(lean_object* v_builder_1204_, lean_object* v_uri_1205_){
_start:
{
lean_object* v___y_1207_; lean_object* v___f_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___f_1228_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__1));
v___x_1229_ = lean_string_to_utf8(v_uri_1205_);
v___x_1230_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1228_, v___x_1229_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_dec_ref_known(v___x_1230_, 1);
v___x_1231_ = lean_obj_once(&l_Std_Http_Request_Builder_uri_x21___closed__5, &l_Std_Http_Request_Builder_uri_x21___closed__5_once, _init_l_Std_Http_Request_Builder_uri_x21___closed__5);
v___x_1232_ = l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(v___x_1231_);
v___y_1207_ = v___x_1232_;
goto v___jp_1206_;
}
else
{
lean_object* v_a_1233_; 
v_a_1233_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1230_, 1);
v___y_1207_ = v_a_1233_;
goto v___jp_1206_;
}
v___jp_1206_:
{
lean_object* v_line_1208_; lean_object* v_extensions_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1227_; 
v_line_1208_ = lean_ctor_get(v_builder_1204_, 0);
v_extensions_1209_ = lean_ctor_get(v_builder_1204_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_builder_1204_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1211_ = v_builder_1204_;
v_isShared_1212_ = v_isSharedCheck_1227_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_extensions_1209_);
lean_inc(v_line_1208_);
lean_dec(v_builder_1204_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1227_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
uint8_t v_method_1213_; uint8_t v_version_1214_; lean_object* v_headers_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1225_; 
v_method_1213_ = lean_ctor_get_uint8(v_line_1208_, sizeof(void*)*2);
v_version_1214_ = lean_ctor_get_uint8(v_line_1208_, sizeof(void*)*2 + 1);
v_headers_1215_ = lean_ctor_get(v_line_1208_, 1);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_line_1208_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v_line_1208_, 0);
lean_dec(v_unused_1226_);
v___x_1217_ = v_line_1208_;
v_isShared_1218_ = v_isSharedCheck_1225_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_headers_1215_);
lean_dec(v_line_1208_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1225_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___y_1207_);
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___y_1207_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_headers_1215_);
lean_ctor_set_uint8(v_reuseFailAlloc_1224_, sizeof(void*)*2, v_method_1213_);
lean_ctor_set_uint8(v_reuseFailAlloc_1224_, sizeof(void*)*2 + 1, v_version_1214_);
v___x_1220_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1222_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v___x_1220_);
v___x_1222_ = v___x_1211_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_extensions_1209_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___boxed(lean_object* v_builder_1234_, lean_object* v_uri_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Std_Http_Request_Builder_uri_x21(v_builder_1234_, v_uri_1235_);
lean_dec_ref(v_uri_1235_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headers(lean_object* v_builder_1237_, lean_object* v_headers_1238_){
_start:
{
lean_object* v_line_1239_; lean_object* v_extensions_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1258_; 
v_line_1239_ = lean_ctor_get(v_builder_1237_, 0);
v_extensions_1240_ = lean_ctor_get(v_builder_1237_, 1);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_builder_1237_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1242_ = v_builder_1237_;
v_isShared_1243_ = v_isSharedCheck_1258_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_extensions_1240_);
lean_inc(v_line_1239_);
lean_dec(v_builder_1237_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1258_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
uint8_t v_method_1244_; uint8_t v_version_1245_; lean_object* v_uri_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1256_; 
v_method_1244_ = lean_ctor_get_uint8(v_line_1239_, sizeof(void*)*2);
v_version_1245_ = lean_ctor_get_uint8(v_line_1239_, sizeof(void*)*2 + 1);
v_uri_1246_ = lean_ctor_get(v_line_1239_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_line_1239_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v_line_1239_, 1);
lean_dec(v_unused_1257_);
v___x_1248_ = v_line_1239_;
v_isShared_1249_ = v_isSharedCheck_1256_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_uri_1246_);
lean_dec(v_line_1239_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1256_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v_headers_1238_);
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_uri_1246_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_headers_1238_);
lean_ctor_set_uint8(v_reuseFailAlloc_1255_, sizeof(void*)*2, v_method_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1255_, sizeof(void*)*2 + 1, v_version_1245_);
v___x_1251_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1253_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1251_);
v___x_1253_ = v___x_1242_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_extensions_1240_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(lean_object* v_i_1259_, lean_object* v_x_1260_){
_start:
{
if (lean_obj_tag(v_x_1260_) == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1261_ = lean_unsigned_to_nat(1u);
v___x_1262_ = lean_mk_empty_array_with_capacity(v___x_1261_);
v___x_1263_ = lean_array_push(v___x_1262_, v_i_1259_);
v___x_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
return v___x_1264_;
}
else
{
lean_object* v_val_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1273_; 
v_val_1265_ = lean_ctor_get(v_x_1260_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_x_1260_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1267_ = v_x_1260_;
v_isShared_1268_ = v_isSharedCheck_1273_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_val_1265_);
lean_dec(v_x_1260_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1273_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1269_ = lean_array_push(v_val_1265_, v_i_1259_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1269_);
v___x_1271_ = v___x_1267_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(lean_object* v_i_1274_, lean_object* v_a_1275_, lean_object* v_x_1276_){
_start:
{
if (lean_obj_tag(v_x_1276_) == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v_val_1279_; lean_object* v___x_1280_; 
v___x_1277_ = lean_box(0);
v___x_1278_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(v_i_1274_, v___x_1277_);
v_val_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_val_1279_);
lean_dec(v___x_1278_);
v___x_1280_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1280_, 0, v_a_1275_);
lean_ctor_set(v___x_1280_, 1, v_val_1279_);
lean_ctor_set(v___x_1280_, 2, v_x_1276_);
return v___x_1280_;
}
else
{
lean_object* v_key_1281_; lean_object* v_value_1282_; lean_object* v_tail_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1298_; 
v_key_1281_ = lean_ctor_get(v_x_1276_, 0);
v_value_1282_ = lean_ctor_get(v_x_1276_, 1);
v_tail_1283_ = lean_ctor_get(v_x_1276_, 2);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_x_1276_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1285_ = v_x_1276_;
v_isShared_1286_ = v_isSharedCheck_1298_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_tail_1283_);
lean_inc(v_value_1282_);
lean_inc(v_key_1281_);
lean_dec(v_x_1276_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1298_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_string_dec_eq(v_key_1281_, v_a_1275_);
if (v___x_1287_ == 0)
{
lean_object* v_tail_1288_; lean_object* v___x_1290_; 
v_tail_1288_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_1274_, v_a_1275_, v_tail_1283_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 2, v_tail_1288_);
v___x_1290_ = v___x_1285_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_key_1281_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_value_1282_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_tail_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
else
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v_val_1294_; lean_object* v___x_1296_; 
lean_dec(v_key_1281_);
v___x_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1292_, 0, v_value_1282_);
v___x_1293_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(v_i_1274_, v___x_1292_);
v_val_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_val_1294_);
lean_dec(v___x_1293_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v_val_1294_);
lean_ctor_set(v___x_1285_, 0, v_a_1275_);
v___x_1296_ = v___x_1285_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1275_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_val_1294_);
lean_ctor_set(v_reuseFailAlloc_1297_, 2, v_tail_1283_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(lean_object* v_a_1299_, lean_object* v_x_1300_){
_start:
{
if (lean_obj_tag(v_x_1300_) == 0)
{
uint8_t v___x_1301_; 
v___x_1301_ = 0;
return v___x_1301_;
}
else
{
lean_object* v_key_1302_; lean_object* v_tail_1303_; uint8_t v___x_1304_; 
v_key_1302_ = lean_ctor_get(v_x_1300_, 0);
v_tail_1303_ = lean_ctor_get(v_x_1300_, 2);
v___x_1304_ = lean_string_dec_eq(v_key_1302_, v_a_1299_);
if (v___x_1304_ == 0)
{
v_x_1300_ = v_tail_1303_;
goto _start;
}
else
{
return v___x_1304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg___boxed(lean_object* v_a_1306_, lean_object* v_x_1307_){
_start:
{
uint8_t v_res_1308_; lean_object* v_r_1309_; 
v_res_1308_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1306_, v_x_1307_);
lean_dec(v_x_1307_);
lean_dec_ref(v_a_1306_);
v_r_1309_ = lean_box(v_res_1308_);
return v_r_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1310_, lean_object* v_x_1311_){
_start:
{
if (lean_obj_tag(v_x_1311_) == 0)
{
return v_x_1310_;
}
else
{
lean_object* v_key_1312_; lean_object* v_value_1313_; lean_object* v_tail_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1337_; 
v_key_1312_ = lean_ctor_get(v_x_1311_, 0);
v_value_1313_ = lean_ctor_get(v_x_1311_, 1);
v_tail_1314_ = lean_ctor_get(v_x_1311_, 2);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_x_1311_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1316_ = v_x_1311_;
v_isShared_1317_ = v_isSharedCheck_1337_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_tail_1314_);
lean_inc(v_value_1313_);
lean_inc(v_key_1312_);
lean_dec(v_x_1311_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1337_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; uint64_t v___x_1319_; uint64_t v___x_1320_; uint64_t v___x_1321_; uint64_t v_fold_1322_; uint64_t v___x_1323_; uint64_t v___x_1324_; uint64_t v___x_1325_; size_t v___x_1326_; size_t v___x_1327_; size_t v___x_1328_; size_t v___x_1329_; size_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1318_ = lean_array_get_size(v_x_1310_);
v___x_1319_ = lean_string_hash(v_key_1312_);
v___x_1320_ = 32ULL;
v___x_1321_ = lean_uint64_shift_right(v___x_1319_, v___x_1320_);
v_fold_1322_ = lean_uint64_xor(v___x_1319_, v___x_1321_);
v___x_1323_ = 16ULL;
v___x_1324_ = lean_uint64_shift_right(v_fold_1322_, v___x_1323_);
v___x_1325_ = lean_uint64_xor(v_fold_1322_, v___x_1324_);
v___x_1326_ = lean_uint64_to_usize(v___x_1325_);
v___x_1327_ = lean_usize_of_nat(v___x_1318_);
v___x_1328_ = ((size_t)1ULL);
v___x_1329_ = lean_usize_sub(v___x_1327_, v___x_1328_);
v___x_1330_ = lean_usize_land(v___x_1326_, v___x_1329_);
v___x_1331_ = lean_array_uget_borrowed(v_x_1310_, v___x_1330_);
lean_inc(v___x_1331_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 2, v___x_1331_);
v___x_1333_ = v___x_1316_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_key_1312_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_value_1313_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_array_uset(v_x_1310_, v___x_1330_, v___x_1333_);
v_x_1310_ = v___x_1334_;
v_x_1311_ = v_tail_1314_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1338_, lean_object* v_source_1339_, lean_object* v_target_1340_){
_start:
{
lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = lean_array_get_size(v_source_1339_);
v___x_1342_ = lean_nat_dec_lt(v_i_1338_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_dec_ref(v_source_1339_);
lean_dec(v_i_1338_);
return v_target_1340_;
}
else
{
lean_object* v_es_1343_; lean_object* v___x_1344_; lean_object* v_source_1345_; lean_object* v_target_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v_es_1343_ = lean_array_fget(v_source_1339_, v_i_1338_);
v___x_1344_ = lean_box(0);
v_source_1345_ = lean_array_fset(v_source_1339_, v_i_1338_, v___x_1344_);
v_target_1346_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1340_, v_es_1343_);
v___x_1347_ = lean_unsigned_to_nat(1u);
v___x_1348_ = lean_nat_add(v_i_1338_, v___x_1347_);
lean_dec(v_i_1338_);
v_i_1338_ = v___x_1348_;
v_source_1339_ = v_source_1345_;
v_target_1340_ = v_target_1346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(lean_object* v_data_1350_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v_nbuckets_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1351_ = lean_array_get_size(v_data_1350_);
v___x_1352_ = lean_unsigned_to_nat(2u);
v_nbuckets_1353_ = lean_nat_mul(v___x_1351_, v___x_1352_);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = lean_box(0);
v___x_1356_ = lean_mk_array(v_nbuckets_1353_, v___x_1355_);
v___x_1357_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v___x_1354_, v_data_1350_, v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(lean_object* v_i_1358_, lean_object* v_m_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_size_1361_; lean_object* v_buckets_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1412_; 
v_size_1361_ = lean_ctor_get(v_m_1359_, 0);
v_buckets_1362_ = lean_ctor_get(v_m_1359_, 1);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_m_1359_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1364_ = v_m_1359_;
v_isShared_1365_ = v_isSharedCheck_1412_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_buckets_1362_);
lean_inc(v_size_1361_);
lean_dec(v_m_1359_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1412_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; uint64_t v___x_1367_; uint64_t v___x_1368_; uint64_t v___x_1369_; uint64_t v_fold_1370_; uint64_t v___x_1371_; uint64_t v___x_1372_; uint64_t v___x_1373_; size_t v___x_1374_; size_t v___x_1375_; size_t v___x_1376_; size_t v___x_1377_; size_t v___x_1378_; lean_object* v_bkt_1379_; uint8_t v___x_1380_; 
v___x_1366_ = lean_array_get_size(v_buckets_1362_);
v___x_1367_ = lean_string_hash(v_a_1360_);
v___x_1368_ = 32ULL;
v___x_1369_ = lean_uint64_shift_right(v___x_1367_, v___x_1368_);
v_fold_1370_ = lean_uint64_xor(v___x_1367_, v___x_1369_);
v___x_1371_ = 16ULL;
v___x_1372_ = lean_uint64_shift_right(v_fold_1370_, v___x_1371_);
v___x_1373_ = lean_uint64_xor(v_fold_1370_, v___x_1372_);
v___x_1374_ = lean_uint64_to_usize(v___x_1373_);
v___x_1375_ = lean_usize_of_nat(v___x_1366_);
v___x_1376_ = ((size_t)1ULL);
v___x_1377_ = lean_usize_sub(v___x_1375_, v___x_1376_);
v___x_1378_ = lean_usize_land(v___x_1374_, v___x_1377_);
v_bkt_1379_ = lean_array_uget_borrowed(v_buckets_1362_, v___x_1378_);
v___x_1380_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1360_, v_bkt_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v_size_x27_1384_; lean_object* v___x_1385_; lean_object* v_buckets_x27_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1381_ = lean_unsigned_to_nat(1u);
v___x_1382_ = lean_mk_empty_array_with_capacity(v___x_1381_);
v___x_1383_ = lean_array_push(v___x_1382_, v_i_1358_);
v_size_x27_1384_ = lean_nat_add(v_size_1361_, v___x_1381_);
lean_dec(v_size_1361_);
lean_inc(v_bkt_1379_);
v___x_1385_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1385_, 0, v_a_1360_);
lean_ctor_set(v___x_1385_, 1, v___x_1383_);
lean_ctor_set(v___x_1385_, 2, v_bkt_1379_);
v_buckets_x27_1386_ = lean_array_uset(v_buckets_1362_, v___x_1378_, v___x_1385_);
v___x_1387_ = lean_unsigned_to_nat(4u);
v___x_1388_ = lean_nat_mul(v_size_x27_1384_, v___x_1387_);
v___x_1389_ = lean_unsigned_to_nat(3u);
v___x_1390_ = lean_nat_div(v___x_1388_, v___x_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_array_get_size(v_buckets_x27_1386_);
v___x_1392_ = lean_nat_dec_le(v___x_1390_, v___x_1391_);
lean_dec(v___x_1390_);
if (v___x_1392_ == 0)
{
lean_object* v_val_1393_; lean_object* v___x_1395_; 
v_val_1393_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_buckets_x27_1386_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v_val_1393_);
lean_ctor_set(v___x_1364_, 0, v_size_x27_1384_);
v___x_1395_ = v___x_1364_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_size_x27_1384_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_val_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
else
{
lean_object* v___x_1398_; 
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v_buckets_x27_1386_);
lean_ctor_set(v___x_1364_, 0, v_size_x27_1384_);
v___x_1398_ = v___x_1364_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_size_x27_1384_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_buckets_x27_1386_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
else
{
lean_object* v___x_1400_; lean_object* v_buckets_x27_1401_; lean_object* v_bkt_x27_1402_; lean_object* v___y_1404_; uint8_t v___x_1409_; 
lean_inc(v_bkt_1379_);
v___x_1400_ = lean_box(0);
v_buckets_x27_1401_ = lean_array_uset(v_buckets_1362_, v___x_1378_, v___x_1400_);
lean_inc_ref(v_a_1360_);
v_bkt_x27_1402_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_1358_, v_a_1360_, v_bkt_1379_);
v___x_1409_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1360_, v_bkt_x27_1402_);
lean_dec_ref(v_a_1360_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_unsigned_to_nat(1u);
v___x_1411_ = lean_nat_sub(v_size_1361_, v___x_1410_);
lean_dec(v_size_1361_);
v___y_1404_ = v___x_1411_;
goto v___jp_1403_;
}
else
{
v___y_1404_ = v_size_1361_;
goto v___jp_1403_;
}
v___jp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1405_ = lean_array_uset(v_buckets_x27_1401_, v___x_1378_, v_bkt_x27_1402_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v___x_1405_);
lean_ctor_set(v___x_1364_, 0, v___y_1404_);
v___x_1407_ = v___x_1364_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___y_1404_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header(lean_object* v_builder_1413_, lean_object* v_key_1414_, lean_object* v_value_1415_){
_start:
{
lean_object* v_line_1416_; lean_object* v_headers_1417_; lean_object* v_extensions_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1449_; 
v_line_1416_ = lean_ctor_get(v_builder_1413_, 0);
lean_inc_ref(v_line_1416_);
v_headers_1417_ = lean_ctor_get(v_line_1416_, 1);
lean_inc_ref(v_headers_1417_);
v_extensions_1418_ = lean_ctor_get(v_builder_1413_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_builder_1413_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; 
v_unused_1450_ = lean_ctor_get(v_builder_1413_, 0);
lean_dec(v_unused_1450_);
v___x_1420_ = v_builder_1413_;
v_isShared_1421_ = v_isSharedCheck_1449_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_extensions_1418_);
lean_dec(v_builder_1413_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1449_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
uint8_t v_method_1422_; uint8_t v_version_1423_; lean_object* v_uri_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1447_; 
v_method_1422_ = lean_ctor_get_uint8(v_line_1416_, sizeof(void*)*2);
v_version_1423_ = lean_ctor_get_uint8(v_line_1416_, sizeof(void*)*2 + 1);
v_uri_1424_ = lean_ctor_get(v_line_1416_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_line_1416_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; 
v_unused_1448_ = lean_ctor_get(v_line_1416_, 1);
lean_dec(v_unused_1448_);
v___x_1426_ = v_line_1416_;
v_isShared_1427_ = v_isSharedCheck_1447_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_uri_1424_);
lean_dec(v_line_1416_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1447_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v_entries_1428_; lean_object* v_indexes_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1446_; 
v_entries_1428_ = lean_ctor_get(v_headers_1417_, 0);
v_indexes_1429_ = lean_ctor_get(v_headers_1417_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_headers_1417_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1431_ = v_headers_1417_;
v_isShared_1432_ = v_isSharedCheck_1446_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_indexes_1429_);
lean_inc(v_entries_1428_);
lean_dec(v_headers_1417_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1446_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_i_1433_; lean_object* v___x_1434_; lean_object* v_entries_1435_; lean_object* v_indexes_1436_; lean_object* v___x_1438_; 
v_i_1433_ = lean_array_get_size(v_entries_1428_);
lean_inc_ref(v_key_1414_);
v___x_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1434_, 0, v_key_1414_);
lean_ctor_set(v___x_1434_, 1, v_value_1415_);
v_entries_1435_ = lean_array_push(v_entries_1428_, v___x_1434_);
v_indexes_1436_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1433_, v_indexes_1429_, v_key_1414_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v_indexes_1436_);
lean_ctor_set(v___x_1431_, 0, v_entries_1435_);
v___x_1438_ = v___x_1431_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_entries_1435_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_indexes_1436_);
v___x_1438_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1440_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v___x_1438_);
v___x_1440_ = v___x_1426_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_uri_1424_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v___x_1438_);
lean_ctor_set_uint8(v_reuseFailAlloc_1444_, sizeof(void*)*2, v_method_1422_);
lean_ctor_set_uint8(v_reuseFailAlloc_1444_, sizeof(void*)*2 + 1, v_version_1423_);
v___x_1440_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1442_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1440_);
v___x_1442_ = v___x_1420_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_extensions_1418_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(lean_object* v_00_u03b2_1451_, lean_object* v_a_1452_, lean_object* v_x_1453_){
_start:
{
uint8_t v___x_1454_; 
v___x_1454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1452_, v_x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1455_, lean_object* v_a_1456_, lean_object* v_x_1457_){
_start:
{
uint8_t v_res_1458_; lean_object* v_r_1459_; 
v_res_1458_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(v_00_u03b2_1455_, v_a_1456_, v_x_1457_);
lean_dec(v_x_1457_);
lean_dec_ref(v_a_1456_);
v_r_1459_ = lean_box(v_res_1458_);
return v_r_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1(lean_object* v_00_u03b2_1460_, lean_object* v_data_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_data_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1463_, lean_object* v_i_1464_, lean_object* v_source_1465_, lean_object* v_target_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v_i_1464_, v_source_1465_, v_target_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1468_, lean_object* v_x_1469_, lean_object* v_x_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1469_, v_x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x21(lean_object* v_builder_1472_, lean_object* v_key_1473_, lean_object* v_value_1474_){
_start:
{
lean_object* v_line_1475_; lean_object* v_headers_1476_; lean_object* v_extensions_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1510_; 
v_line_1475_ = lean_ctor_get(v_builder_1472_, 0);
lean_inc_ref(v_line_1475_);
v_headers_1476_ = lean_ctor_get(v_line_1475_, 1);
lean_inc_ref(v_headers_1476_);
v_extensions_1477_ = lean_ctor_get(v_builder_1472_, 1);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_builder_1472_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v_builder_1472_, 0);
lean_dec(v_unused_1511_);
v___x_1479_ = v_builder_1472_;
v_isShared_1480_ = v_isSharedCheck_1510_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_extensions_1477_);
lean_dec(v_builder_1472_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1510_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
uint8_t v_method_1481_; uint8_t v_version_1482_; lean_object* v_uri_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1508_; 
v_method_1481_ = lean_ctor_get_uint8(v_line_1475_, sizeof(void*)*2);
v_version_1482_ = lean_ctor_get_uint8(v_line_1475_, sizeof(void*)*2 + 1);
v_uri_1483_ = lean_ctor_get(v_line_1475_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_line_1475_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; 
v_unused_1509_ = lean_ctor_get(v_line_1475_, 1);
lean_dec(v_unused_1509_);
v___x_1485_ = v_line_1475_;
v_isShared_1486_ = v_isSharedCheck_1508_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_uri_1483_);
lean_dec(v_line_1475_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1508_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v_entries_1487_; lean_object* v_indexes_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1507_; 
v_entries_1487_ = lean_ctor_get(v_headers_1476_, 0);
v_indexes_1488_ = lean_ctor_get(v_headers_1476_, 1);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_headers_1476_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1490_ = v_headers_1476_;
v_isShared_1491_ = v_isSharedCheck_1507_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_indexes_1488_);
lean_inc(v_entries_1487_);
lean_dec(v_headers_1476_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1507_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_key_1492_; lean_object* v_value_1493_; lean_object* v_i_1494_; lean_object* v___x_1495_; lean_object* v_entries_1496_; lean_object* v_indexes_1497_; lean_object* v___x_1499_; 
v_key_1492_ = l_Std_Http_Header_Name_ofString_x21(v_key_1473_);
v_value_1493_ = l_Std_Http_Header_Value_ofString_x21(v_value_1474_);
v_i_1494_ = lean_array_get_size(v_entries_1487_);
lean_inc_ref(v_key_1492_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_key_1492_);
lean_ctor_set(v___x_1495_, 1, v_value_1493_);
v_entries_1496_ = lean_array_push(v_entries_1487_, v___x_1495_);
v_indexes_1497_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1494_, v_indexes_1488_, v_key_1492_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v_indexes_1497_);
lean_ctor_set(v___x_1490_, 0, v_entries_1496_);
v___x_1499_ = v___x_1490_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_entries_1496_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_indexes_1497_);
v___x_1499_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1501_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 1, v___x_1499_);
v___x_1501_ = v___x_1485_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_uri_1483_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v___x_1499_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, sizeof(void*)*2, v_method_1481_);
lean_ctor_set_uint8(v_reuseFailAlloc_1505_, sizeof(void*)*2 + 1, v_version_1482_);
v___x_1501_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1503_; 
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v___x_1501_);
v___x_1503_ = v___x_1479_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_extensions_1477_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x3f(lean_object* v_builder_1512_, lean_object* v_key_1513_, lean_object* v_value_1514_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Std_Http_Header_Name_ofString_x3f(v_key_1513_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v___x_1516_; 
lean_dec_ref(v_value_1514_);
lean_dec_ref(v_builder_1512_);
v___x_1516_ = lean_box(0);
return v___x_1516_;
}
else
{
lean_object* v_val_1517_; lean_object* v___x_1518_; 
v_val_1517_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_val_1517_);
lean_dec_ref_known(v___x_1515_, 1);
v___x_1518_ = l_Std_Http_Header_Value_ofString_x3f(v_value_1514_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v___x_1519_; 
lean_dec(v_val_1517_);
lean_dec_ref(v_builder_1512_);
v___x_1519_ = lean_box(0);
return v___x_1519_;
}
else
{
lean_object* v_line_1520_; lean_object* v_headers_1521_; lean_object* v_val_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1562_; 
v_line_1520_ = lean_ctor_get(v_builder_1512_, 0);
lean_inc_ref(v_line_1520_);
v_headers_1521_ = lean_ctor_get(v_line_1520_, 1);
lean_inc_ref(v_headers_1521_);
v_val_1522_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1524_ = v___x_1518_;
v_isShared_1525_ = v_isSharedCheck_1562_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_val_1522_);
lean_dec(v___x_1518_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1562_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v_extensions_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1560_; 
v_extensions_1526_ = lean_ctor_get(v_builder_1512_, 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_builder_1512_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v_builder_1512_, 0);
lean_dec(v_unused_1561_);
v___x_1528_ = v_builder_1512_;
v_isShared_1529_ = v_isSharedCheck_1560_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_extensions_1526_);
lean_dec(v_builder_1512_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1560_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
uint8_t v_method_1530_; uint8_t v_version_1531_; lean_object* v_uri_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1558_; 
v_method_1530_ = lean_ctor_get_uint8(v_line_1520_, sizeof(void*)*2);
v_version_1531_ = lean_ctor_get_uint8(v_line_1520_, sizeof(void*)*2 + 1);
v_uri_1532_ = lean_ctor_get(v_line_1520_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_line_1520_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; 
v_unused_1559_ = lean_ctor_get(v_line_1520_, 1);
lean_dec(v_unused_1559_);
v___x_1534_ = v_line_1520_;
v_isShared_1535_ = v_isSharedCheck_1558_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_uri_1532_);
lean_dec(v_line_1520_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1558_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v_entries_1536_; lean_object* v_indexes_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1557_; 
v_entries_1536_ = lean_ctor_get(v_headers_1521_, 0);
v_indexes_1537_ = lean_ctor_get(v_headers_1521_, 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_headers_1521_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1539_ = v_headers_1521_;
v_isShared_1540_ = v_isSharedCheck_1557_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_indexes_1537_);
lean_inc(v_entries_1536_);
lean_dec(v_headers_1521_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1557_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v_i_1541_; lean_object* v___x_1542_; lean_object* v_entries_1543_; lean_object* v_indexes_1544_; lean_object* v___x_1546_; 
v_i_1541_ = lean_array_get_size(v_entries_1536_);
lean_inc(v_val_1517_);
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v_val_1517_);
lean_ctor_set(v___x_1542_, 1, v_val_1522_);
v_entries_1543_ = lean_array_push(v_entries_1536_, v___x_1542_);
v_indexes_1544_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1541_, v_indexes_1537_, v_val_1517_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 1, v_indexes_1544_);
lean_ctor_set(v___x_1539_, 0, v_entries_1543_);
v___x_1546_ = v___x_1539_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_entries_1543_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_indexes_1544_);
v___x_1546_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1548_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 1, v___x_1546_);
v___x_1548_ = v___x_1534_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_uri_1532_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v___x_1546_);
lean_ctor_set_uint8(v_reuseFailAlloc_1555_, sizeof(void*)*2, v_method_1530_);
lean_ctor_set_uint8(v_reuseFailAlloc_1555_, sizeof(void*)*2 + 1, v_version_1531_);
v___x_1548_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1550_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v___x_1548_);
v___x_1550_ = v___x_1528_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_extensions_1526_);
v___x_1550_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1552_; 
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1550_);
v___x_1552_ = v___x_1524_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
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
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headerOpt(lean_object* v_builder_1563_, lean_object* v_key_1564_, lean_object* v_value_1565_){
_start:
{
if (lean_obj_tag(v_value_1565_) == 0)
{
lean_dec_ref(v_key_1564_);
return v_builder_1563_;
}
else
{
lean_object* v_val_1566_; lean_object* v___x_1567_; 
v_val_1566_ = lean_ctor_get(v_value_1565_, 0);
lean_inc(v_val_1566_);
lean_dec_ref_known(v_value_1565_, 1);
v___x_1567_ = l_Std_Http_Request_Builder_header(v_builder_1563_, v_key_1564_, v_val_1566_);
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension___redArg(lean_object* v_builder_1569_, lean_object* v_inst_1570_, lean_object* v_data_1571_){
_start:
{
lean_object* v_line_1572_; lean_object* v_extensions_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1584_; 
v_line_1572_ = lean_ctor_get(v_builder_1569_, 0);
v_extensions_1573_ = lean_ctor_get(v_builder_1569_, 1);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_builder_1569_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1575_ = v_builder_1569_;
v_isShared_1576_ = v_isSharedCheck_1584_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_extensions_1573_);
lean_inc(v_line_1572_);
lean_dec(v_builder_1569_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1584_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v_dyn_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
v_dyn_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_1577_, 0, v_inst_1570_);
lean_ctor_set(v_dyn_1577_, 1, v_data_1571_);
v___x_1578_ = ((lean_object*)(l_Std_Http_Request_Builder_extension___redArg___closed__0));
v___x_1579_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_1577_);
v___x_1580_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1578_, v___x_1579_, v_dyn_1577_, v_extensions_1573_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 1, v___x_1580_);
v___x_1582_ = v___x_1575_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_line_1572_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension(lean_object* v_00_u03b1_1585_, lean_object* v_builder_1586_, lean_object* v_inst_1587_, lean_object* v_data_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Std_Http_Request_Builder_extension___redArg(v_builder_1586_, v_inst_1587_, v_data_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object* v_builder_1590_, lean_object* v_body_1591_){
_start:
{
lean_object* v_line_1592_; lean_object* v_extensions_1593_; lean_object* v___x_1594_; 
v_line_1592_ = lean_ctor_get(v_builder_1590_, 0);
v_extensions_1593_ = lean_ctor_get(v_builder_1590_, 1);
lean_inc(v_extensions_1593_);
lean_inc_ref(v_line_1592_);
v___x_1594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1594_, 0, v_line_1592_);
lean_ctor_set(v___x_1594_, 1, v_body_1591_);
lean_ctor_set(v___x_1594_, 2, v_extensions_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg___boxed(lean_object* v_builder_1595_, lean_object* v_body_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1595_, v_body_1596_);
lean_dec_ref(v_builder_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body(lean_object* v_t_1598_, lean_object* v_builder_1599_, lean_object* v_body_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1599_, v_body_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___boxed(lean_object* v_t_1602_, lean_object* v_builder_1603_, lean_object* v_body_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Std_Http_Request_Builder_body(v_t_1602_, v_builder_1603_, v_body_1604_);
lean_dec_ref(v_builder_1603_);
return v_res_1605_;
}
}
static lean_object* _init_l_Std_Http_Request_get___closed__0(void){
_start:
{
uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1606_ = 8;
v___x_1607_ = l_Std_Http_Request_new;
v___x_1608_ = l_Std_Http_Request_Builder_method(v___x_1607_, v___x_1606_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_get(lean_object* v_uri_1609_){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_obj_once(&l_Std_Http_Request_get___closed__0, &l_Std_Http_Request_get___closed__0_once, _init_l_Std_Http_Request_get___closed__0);
v___x_1611_ = l_Std_Http_Request_Builder_uri(v___x_1610_, v_uri_1609_);
return v___x_1611_;
}
}
static lean_object* _init_l_Std_Http_Request_post___closed__0(void){
_start:
{
uint8_t v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = 23;
v___x_1613_ = l_Std_Http_Request_new;
v___x_1614_ = l_Std_Http_Request_Builder_method(v___x_1613_, v___x_1612_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_post(lean_object* v_uri_1615_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_obj_once(&l_Std_Http_Request_post___closed__0, &l_Std_Http_Request_post___closed__0_once, _init_l_Std_Http_Request_post___closed__0);
v___x_1617_ = l_Std_Http_Request_Builder_uri(v___x_1616_, v_uri_1615_);
return v___x_1617_;
}
}
static lean_object* _init_l_Std_Http_Request_put___closed__0(void){
_start:
{
uint8_t v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1618_ = 27;
v___x_1619_ = l_Std_Http_Request_new;
v___x_1620_ = l_Std_Http_Request_Builder_method(v___x_1619_, v___x_1618_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_put(lean_object* v_uri_1621_){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_obj_once(&l_Std_Http_Request_put___closed__0, &l_Std_Http_Request_put___closed__0_once, _init_l_Std_Http_Request_put___closed__0);
v___x_1623_ = l_Std_Http_Request_Builder_uri(v___x_1622_, v_uri_1621_);
return v___x_1623_;
}
}
static lean_object* _init_l_Std_Http_Request_delete___closed__0(void){
_start:
{
uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1624_ = 7;
v___x_1625_ = l_Std_Http_Request_new;
v___x_1626_ = l_Std_Http_Request_Builder_method(v___x_1625_, v___x_1624_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_delete(lean_object* v_uri_1627_){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = lean_obj_once(&l_Std_Http_Request_delete___closed__0, &l_Std_Http_Request_delete___closed__0_once, _init_l_Std_Http_Request_delete___closed__0);
v___x_1629_ = l_Std_Http_Request_Builder_uri(v___x_1628_, v_uri_1627_);
return v___x_1629_;
}
}
static lean_object* _init_l_Std_Http_Request_patch___closed__0(void){
_start:
{
uint8_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = 22;
v___x_1631_ = l_Std_Http_Request_new;
v___x_1632_ = l_Std_Http_Request_Builder_method(v___x_1631_, v___x_1630_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_patch(lean_object* v_uri_1633_){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_obj_once(&l_Std_Http_Request_patch___closed__0, &l_Std_Http_Request_patch___closed__0_once, _init_l_Std_Http_Request_patch___closed__0);
v___x_1635_ = l_Std_Http_Request_Builder_uri(v___x_1634_, v_uri_1633_);
return v___x_1635_;
}
}
static lean_object* _init_l_Std_Http_Request_head___closed__0(void){
_start:
{
uint8_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1636_ = 9;
v___x_1637_ = l_Std_Http_Request_new;
v___x_1638_ = l_Std_Http_Request_Builder_method(v___x_1637_, v___x_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_head(lean_object* v_uri_1639_){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = lean_obj_once(&l_Std_Http_Request_head___closed__0, &l_Std_Http_Request_head___closed__0_once, _init_l_Std_Http_Request_head___closed__0);
v___x_1641_ = l_Std_Http_Request_Builder_uri(v___x_1640_, v_uri_1639_);
return v___x_1641_;
}
}
static lean_object* _init_l_Std_Http_Request_options___closed__0(void){
_start:
{
uint8_t v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1642_ = 20;
v___x_1643_ = l_Std_Http_Request_new;
v___x_1644_ = l_Std_Http_Request_Builder_method(v___x_1643_, v___x_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_options(lean_object* v_uri_1645_){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_obj_once(&l_Std_Http_Request_options___closed__0, &l_Std_Http_Request_options___closed__0_once, _init_l_Std_Http_Request_options___closed__0);
v___x_1647_ = l_Std_Http_Request_Builder_uri(v___x_1646_, v_uri_1645_);
return v___x_1647_;
}
}
static lean_object* _init_l_Std_Http_Request_connect___closed__0(void){
_start:
{
uint8_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1648_ = 5;
v___x_1649_ = l_Std_Http_Request_new;
v___x_1650_ = l_Std_Http_Request_Builder_method(v___x_1649_, v___x_1648_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_connect(lean_object* v_uri_1651_){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = lean_obj_once(&l_Std_Http_Request_connect___closed__0, &l_Std_Http_Request_connect___closed__0_once, _init_l_Std_Http_Request_connect___closed__0);
v___x_1653_ = l_Std_Http_Request_Builder_uri(v___x_1652_, v_uri_1651_);
return v___x_1653_;
}
}
static lean_object* _init_l_Std_Http_Request_trace___closed__0(void){
_start:
{
uint8_t v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = 32;
v___x_1655_ = l_Std_Http_Request_new;
v___x_1656_ = l_Std_Http_Request_Builder_method(v___x_1655_, v___x_1654_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_trace(lean_object* v_uri_1657_){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_obj_once(&l_Std_Http_Request_trace___closed__0, &l_Std_Http_Request_trace___closed__0_once, _init_l_Std_Http_Request_trace___closed__0);
v___x_1659_ = l_Std_Http_Request_Builder_uri(v___x_1658_, v_uri_1657_);
return v___x_1659_;
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
