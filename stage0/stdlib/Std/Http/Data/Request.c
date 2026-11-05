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
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Http_Internal_appendFieldLine___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Headers_fold___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Extensions_empty;
extern lean_object* l_Std_Http_Headers_empty;
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed(lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_instReprMethod_repr(uint8_t, lean_object*);
lean_object* l_Std_Http_instReprVersion_repr(uint8_t, lean_object*);
lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object*, lean_object*);
lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__1 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__1_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__2 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__2_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__3 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__3_value;
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
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___closed__1;
static const lean_closure_object l_Std_Http_Request_instEncodeV11Head___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_appendFieldLine___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___closed__2 = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__2_value;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___closed__4;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___closed__5;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___closed__6;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___closed__7;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___closed__8;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___closed__9;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___closed__10;
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Request_instEncodeV11Head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instEncodeV11Head___lam__2, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value)} };
static const lean_object* l_Std_Http_Request_instEncodeV11Head___closed__0 = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Request_instEncodeV11Head = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headers(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header(lean_object*, lean_object*, lean_object*);
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
uint8_t v_decide_172_; 
v_decide_172_ = lean_nat_dec_eq(v_searcher_168_, v___x_128_);
if (v_decide_172_ == 0)
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
uint32_t v___x_1518__boxed_202_; lean_object* v_res_203_; 
v___x_1518__boxed_202_ = lean_unbox_uint32(v___x_196_);
lean_dec(v___x_196_);
v_res_203_ = l_Std_Http_Request_instToStringHead___lam__1(v___x_191_, v___x_192_, v___x_193_, v_fst_194_, v___x_195_, v___x_1518__boxed_202_, v___x_197_, v_it_198_, v_acc_199_, v_hP_200_, v_recur_201_);
lean_dec_ref(v___x_197_);
lean_dec_ref(v_fst_194_);
lean_dec(v___x_193_);
lean_dec(v___x_192_);
lean_dec_ref(v___x_191_);
return v_res_203_;
}
}
static lean_object* _init_l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1(void){
_start:
{
uint32_t v___x_208_; lean_object* v___x_209_; 
v___x_208_ = 45;
v___x_209_ = lean_box_uint32(v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2(lean_object* v_x_210_){
_start:
{
lean_object* v_fst_211_; lean_object* v_snd_212_; lean_object* v___y_214_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v_it_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___f_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_fst_211_ = lean_ctor_get(v_x_210_, 0);
lean_inc_n(v_fst_211_, 2);
v_snd_212_ = lean_ctor_get(v_x_210_, 1);
lean_inc(v_snd_212_);
lean_dec_ref(v_x_210_);
v___f_218_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__1));
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_string_utf8_byte_size(v_fst_211_);
v___x_221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_221_, 0, v_fst_211_);
lean_ctor_set(v___x_221_, 1, v___x_219_);
lean_ctor_set(v___x_221_, 2, v___x_220_);
lean_inc_ref(v___x_221_);
v_it_222_ = l_String_Slice_splitToSubslice___redArg(v___x_221_, v___f_218_);
v___x_223_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__2));
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1;
v___f_226_ = lean_alloc_closure((void*)(l_Std_Http_Request_instToStringHead___lam__1___boxed), 11, 7);
lean_closure_set(v___f_226_, 0, v___x_223_);
lean_closure_set(v___f_226_, 1, v___x_219_);
lean_closure_set(v___f_226_, 2, v___x_224_);
lean_closure_set(v___f_226_, 3, v_fst_211_);
lean_closure_set(v___f_226_, 4, v___x_220_);
lean_closure_set(v___f_226_, 5, v___x_225_);
lean_closure_set(v___f_226_, 6, v___x_221_);
v___x_227_ = lean_box(0);
v___x_228_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_226_, v_it_222_, v___x_227_, lean_box(0));
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v___x_229_; 
v___x_229_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_214_ = v___x_229_;
goto v___jp_213_;
}
else
{
lean_object* v_val_230_; 
v_val_230_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_230_);
lean_dec_ref_known(v___x_228_, 1);
v___y_214_ = v_val_230_;
goto v___jp_213_;
}
v___jp_213_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__0));
v___x_216_ = lean_string_append(v___y_214_, v___x_215_);
v___x_217_ = lean_string_append(v___x_216_, v_snd_212_);
lean_dec(v_snd_212_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__4(lean_object* v___f_304_, lean_object* v___f_305_, lean_object* v___f_306_, lean_object* v_req_307_){
_start:
{
uint8_t v_method_308_; uint8_t v_version_309_; lean_object* v_uri_310_; lean_object* v_headers_311_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v_port_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v_host_423_; lean_object* v_port_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_451_; lean_object* v_port_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_464_; lean_object* v_host_465_; lean_object* v_port_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_479_; 
v_method_308_ = lean_ctor_get_uint8(v_req_307_, sizeof(void*)*2);
v_version_309_ = lean_ctor_get_uint8(v_req_307_, sizeof(void*)*2 + 1);
v_uri_310_ = lean_ctor_get(v_req_307_, 0);
lean_inc(v_uri_310_);
v_headers_311_ = lean_ctor_get(v_req_307_, 1);
lean_inc_ref(v_headers_311_);
lean_dec_ref(v_req_307_);
switch(v_method_308_)
{
case 0:
{
lean_object* v___x_551_; 
v___x_551_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__24));
v___y_479_ = v___x_551_;
goto v___jp_478_;
}
case 1:
{
lean_object* v___x_552_; 
v___x_552_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__25));
v___y_479_ = v___x_552_;
goto v___jp_478_;
}
case 2:
{
lean_object* v___x_553_; 
v___x_553_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__26));
v___y_479_ = v___x_553_;
goto v___jp_478_;
}
case 3:
{
lean_object* v___x_554_; 
v___x_554_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__27));
v___y_479_ = v___x_554_;
goto v___jp_478_;
}
case 4:
{
lean_object* v___x_555_; 
v___x_555_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__28));
v___y_479_ = v___x_555_;
goto v___jp_478_;
}
case 5:
{
lean_object* v___x_556_; 
v___x_556_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__29));
v___y_479_ = v___x_556_;
goto v___jp_478_;
}
case 6:
{
lean_object* v___x_557_; 
v___x_557_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__30));
v___y_479_ = v___x_557_;
goto v___jp_478_;
}
case 7:
{
lean_object* v___x_558_; 
v___x_558_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__31));
v___y_479_ = v___x_558_;
goto v___jp_478_;
}
case 8:
{
lean_object* v___x_559_; 
v___x_559_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__32));
v___y_479_ = v___x_559_;
goto v___jp_478_;
}
case 9:
{
lean_object* v___x_560_; 
v___x_560_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__33));
v___y_479_ = v___x_560_;
goto v___jp_478_;
}
case 10:
{
lean_object* v___x_561_; 
v___x_561_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__34));
v___y_479_ = v___x_561_;
goto v___jp_478_;
}
case 11:
{
lean_object* v___x_562_; 
v___x_562_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__35));
v___y_479_ = v___x_562_;
goto v___jp_478_;
}
case 12:
{
lean_object* v___x_563_; 
v___x_563_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__36));
v___y_479_ = v___x_563_;
goto v___jp_478_;
}
case 13:
{
lean_object* v___x_564_; 
v___x_564_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__37));
v___y_479_ = v___x_564_;
goto v___jp_478_;
}
case 14:
{
lean_object* v___x_565_; 
v___x_565_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__38));
v___y_479_ = v___x_565_;
goto v___jp_478_;
}
case 15:
{
lean_object* v___x_566_; 
v___x_566_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__39));
v___y_479_ = v___x_566_;
goto v___jp_478_;
}
case 16:
{
lean_object* v___x_567_; 
v___x_567_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__40));
v___y_479_ = v___x_567_;
goto v___jp_478_;
}
case 17:
{
lean_object* v___x_568_; 
v___x_568_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__41));
v___y_479_ = v___x_568_;
goto v___jp_478_;
}
case 18:
{
lean_object* v___x_569_; 
v___x_569_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__42));
v___y_479_ = v___x_569_;
goto v___jp_478_;
}
case 19:
{
lean_object* v___x_570_; 
v___x_570_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__43));
v___y_479_ = v___x_570_;
goto v___jp_478_;
}
case 20:
{
lean_object* v___x_571_; 
v___x_571_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__44));
v___y_479_ = v___x_571_;
goto v___jp_478_;
}
case 21:
{
lean_object* v___x_572_; 
v___x_572_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__45));
v___y_479_ = v___x_572_;
goto v___jp_478_;
}
case 22:
{
lean_object* v___x_573_; 
v___x_573_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__46));
v___y_479_ = v___x_573_;
goto v___jp_478_;
}
case 23:
{
lean_object* v___x_574_; 
v___x_574_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__47));
v___y_479_ = v___x_574_;
goto v___jp_478_;
}
case 24:
{
lean_object* v___x_575_; 
v___x_575_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__48));
v___y_479_ = v___x_575_;
goto v___jp_478_;
}
case 25:
{
lean_object* v___x_576_; 
v___x_576_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__49));
v___y_479_ = v___x_576_;
goto v___jp_478_;
}
case 26:
{
lean_object* v___x_577_; 
v___x_577_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__50));
v___y_479_ = v___x_577_;
goto v___jp_478_;
}
case 27:
{
lean_object* v___x_578_; 
v___x_578_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__51));
v___y_479_ = v___x_578_;
goto v___jp_478_;
}
case 28:
{
lean_object* v___x_579_; 
v___x_579_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__52));
v___y_479_ = v___x_579_;
goto v___jp_478_;
}
case 29:
{
lean_object* v___x_580_; 
v___x_580_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__53));
v___y_479_ = v___x_580_;
goto v___jp_478_;
}
case 30:
{
lean_object* v___x_581_; 
v___x_581_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__54));
v___y_479_ = v___x_581_;
goto v___jp_478_;
}
case 31:
{
lean_object* v___x_582_; 
v___x_582_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__55));
v___y_479_ = v___x_582_;
goto v___jp_478_;
}
case 32:
{
lean_object* v___x_583_; 
v___x_583_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__56));
v___y_479_ = v___x_583_;
goto v___jp_478_;
}
case 33:
{
lean_object* v___x_584_; 
v___x_584_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__57));
v___y_479_ = v___x_584_;
goto v___jp_478_;
}
case 34:
{
lean_object* v___x_585_; 
v___x_585_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__58));
v___y_479_ = v___x_585_;
goto v___jp_478_;
}
case 35:
{
lean_object* v___x_586_; 
v___x_586_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__59));
v___y_479_ = v___x_586_;
goto v___jp_478_;
}
case 36:
{
lean_object* v___x_587_; 
v___x_587_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__60));
v___y_479_ = v___x_587_;
goto v___jp_478_;
}
case 37:
{
lean_object* v___x_588_; 
v___x_588_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__61));
v___y_479_ = v___x_588_;
goto v___jp_478_;
}
case 38:
{
lean_object* v___x_589_; 
v___x_589_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__62));
v___y_479_ = v___x_589_;
goto v___jp_478_;
}
default: 
{
lean_object* v___x_590_; 
v___x_590_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__63));
v___y_479_ = v___x_590_;
goto v___jp_478_;
}
}
v___jp_312_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; size_t v_sz_319_; size_t v___x_320_; lean_object* v_pairs_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_315_ = lean_string_append(v___y_313_, v___y_314_);
v___x_316_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__0));
v___x_317_ = lean_string_append(v___x_315_, v___x_316_);
v___x_318_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_319_ = lean_array_size(v_headers_311_);
v___x_320_ = ((size_t)0ULL);
v_pairs_321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_318_, v___f_304_, v_sz_319_, v___x_320_, v_headers_311_);
v___x_322_ = lean_array_to_list(v_pairs_321_);
v___x_323_ = l_String_intercalate(v___x_316_, v___x_322_);
v___x_324_ = lean_string_append(v___x_317_, v___x_323_);
lean_dec_ref(v___x_323_);
v___x_325_ = lean_string_append(v___x_324_, v___x_316_);
return v___x_325_;
}
v___jp_326_:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_string_append(v___y_328_, v___y_329_);
lean_dec_ref(v___y_329_);
v___x_331_ = lean_string_append(v___x_330_, v___y_327_);
switch(v_version_309_)
{
case 0:
{
lean_object* v___x_332_; 
v___x_332_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__11));
v___y_313_ = v___x_331_;
v___y_314_ = v___x_332_;
goto v___jp_312_;
}
case 1:
{
lean_object* v___x_333_; 
v___x_333_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__12));
v___y_313_ = v___x_331_;
v___y_314_ = v___x_333_;
goto v___jp_312_;
}
case 2:
{
lean_object* v___x_334_; 
v___x_334_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__13));
v___y_313_ = v___x_331_;
v___y_314_ = v___x_334_;
goto v___jp_312_;
}
default: 
{
lean_object* v___x_335_; 
v___x_335_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__14));
v___y_313_ = v___x_331_;
v___y_314_ = v___x_335_;
goto v___jp_312_;
}
}
}
v___jp_336_:
{
lean_object* v_queryStr_341_; lean_object* v___x_342_; 
v_queryStr_341_ = l_Std_Http_URI_Query_formatOption(v___y_338_);
v___x_342_ = lean_string_append(v___y_340_, v_queryStr_341_);
lean_dec_ref(v_queryStr_341_);
v___y_327_ = v___y_337_;
v___y_328_ = v___y_339_;
v___y_329_ = v___x_342_;
goto v___jp_326_;
}
v___jp_343_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_351_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_352_ = lean_string_append(v___y_346_, v___x_351_);
v___x_353_ = lean_string_append(v___x_352_, v___y_345_);
lean_dec_ref(v___y_345_);
v___x_354_ = lean_string_append(v___x_353_, v___y_347_);
lean_dec_ref(v___y_347_);
v___x_355_ = lean_string_append(v___x_354_, v___y_348_);
lean_dec_ref(v___y_348_);
v___x_356_ = lean_string_append(v___x_355_, v___y_350_);
lean_dec_ref(v___y_350_);
v___y_327_ = v___y_344_;
v___y_328_ = v___y_349_;
v___y_329_ = v___x_356_;
goto v___jp_326_;
}
v___jp_357_:
{
lean_object* v_queryPart_365_; 
v_queryPart_365_ = l_Std_Http_URI_Query_formatOption(v___y_361_);
if (lean_obj_tag(v___y_362_) == 0)
{
lean_object* v___x_366_; 
v___x_366_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_344_ = v___y_359_;
v___y_345_ = v___y_358_;
v___y_346_ = v___y_360_;
v___y_347_ = v___y_364_;
v___y_348_ = v_queryPart_365_;
v___y_349_ = v___y_363_;
v___y_350_ = v___x_366_;
goto v___jp_343_;
}
else
{
lean_object* v_val_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_val_367_ = lean_ctor_get(v___y_362_, 0);
lean_inc(v_val_367_);
lean_dec_ref_known(v___y_362_, 1);
v___x_368_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__16));
v___x_369_ = l_Std_Http_URI_EncodedFragment_encode(v_val_367_);
v___x_370_ = lean_string_from_utf8_unchecked(v___x_369_);
v___x_371_ = lean_string_append(v___x_368_, v___x_370_);
lean_dec_ref(v___x_370_);
v___y_344_ = v___y_359_;
v___y_345_ = v___y_358_;
v___y_346_ = v___y_360_;
v___y_347_ = v___y_364_;
v___y_348_ = v_queryPart_365_;
v___y_349_ = v___y_363_;
v___y_350_ = v___x_371_;
goto v___jp_343_;
}
}
v___jp_372_:
{
lean_object* v_segments_380_; uint8_t v_absolute_381_; lean_object* v___x_382_; lean_object* v___x_383_; size_t v_sz_384_; size_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v_result_388_; 
v_segments_380_ = lean_ctor_get(v___y_378_, 0);
lean_inc_ref(v_segments_380_);
v_absolute_381_ = lean_ctor_get_uint8(v___y_378_, sizeof(void*)*1);
lean_dec_ref(v___y_378_);
v___x_382_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_383_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_384_ = lean_array_size(v_segments_380_);
v___x_385_ = ((size_t)0ULL);
v___x_386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_383_, v___f_305_, v_sz_384_, v___x_385_, v_segments_380_);
v___x_387_ = lean_array_to_list(v___x_386_);
v_result_388_ = l_String_intercalate(v___x_382_, v___x_387_);
if (v_absolute_381_ == 0)
{
v___y_358_ = v___y_379_;
v___y_359_ = v___y_373_;
v___y_360_ = v___y_375_;
v___y_361_ = v___y_374_;
v___y_362_ = v___y_376_;
v___y_363_ = v___y_377_;
v___y_364_ = v_result_388_;
goto v___jp_357_;
}
else
{
lean_object* v___x_389_; 
v___x_389_ = lean_string_append(v___x_382_, v_result_388_);
lean_dec_ref(v_result_388_);
v___y_358_ = v___y_379_;
v___y_359_ = v___y_373_;
v___y_360_ = v___y_375_;
v___y_361_ = v___y_374_;
v___y_362_ = v___y_376_;
v___y_363_ = v___y_377_;
v___y_364_ = v___x_389_;
goto v___jp_357_;
}
}
v___jp_390_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_401_ = lean_string_append(v___y_397_, v___y_394_);
lean_dec_ref(v___y_394_);
v___x_402_ = lean_string_append(v___x_401_, v___y_400_);
lean_dec_ref(v___y_400_);
lean_inc_ref(v___y_396_);
v___x_403_ = lean_string_append(v___y_396_, v___x_402_);
lean_dec_ref(v___x_402_);
v___y_373_ = v___y_391_;
v___y_374_ = v___y_393_;
v___y_375_ = v___y_392_;
v___y_376_ = v___y_395_;
v___y_377_ = v___y_398_;
v___y_378_ = v___y_399_;
v___y_379_ = v___x_403_;
goto v___jp_372_;
}
v___jp_404_:
{
switch(lean_obj_tag(v_port_405_))
{
case 0:
{
lean_object* v___x_415_; 
v___x_415_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_391_ = v___y_406_;
v___y_392_ = v___y_408_;
v___y_393_ = v___y_407_;
v___y_394_ = v___y_414_;
v___y_395_ = v___y_409_;
v___y_396_ = v___y_410_;
v___y_397_ = v___y_411_;
v___y_398_ = v___y_412_;
v___y_399_ = v___y_413_;
v___y_400_ = v___x_415_;
goto v___jp_390_;
}
case 1:
{
lean_object* v___x_416_; 
v___x_416_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_391_ = v___y_406_;
v___y_392_ = v___y_408_;
v___y_393_ = v___y_407_;
v___y_394_ = v___y_414_;
v___y_395_ = v___y_409_;
v___y_396_ = v___y_410_;
v___y_397_ = v___y_411_;
v___y_398_ = v___y_412_;
v___y_399_ = v___y_413_;
v___y_400_ = v___x_416_;
goto v___jp_390_;
}
default: 
{
uint16_t v_port_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_port_417_ = lean_ctor_get_uint16(v_port_405_, 0);
lean_dec_ref_known(v_port_405_, 0);
v___x_418_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_419_ = lean_uint16_to_nat(v_port_417_);
v___x_420_ = l_Nat_reprFast(v___x_419_);
v___x_421_ = lean_string_append(v___x_418_, v___x_420_);
lean_dec_ref(v___x_420_);
v___y_391_ = v___y_406_;
v___y_392_ = v___y_408_;
v___y_393_ = v___y_407_;
v___y_394_ = v___y_414_;
v___y_395_ = v___y_409_;
v___y_396_ = v___y_410_;
v___y_397_ = v___y_411_;
v___y_398_ = v___y_412_;
v___y_399_ = v___y_413_;
v___y_400_ = v___x_421_;
goto v___jp_390_;
}
}
}
v___jp_422_:
{
switch(lean_obj_tag(v_host_423_))
{
case 0:
{
lean_object* v_name_433_; 
v_name_433_ = lean_ctor_get(v_host_423_, 0);
lean_inc_ref(v_name_433_);
lean_dec_ref_known(v_host_423_, 1);
v_port_405_ = v_port_424_;
v___y_406_ = v___y_425_;
v___y_407_ = v___y_427_;
v___y_408_ = v___y_426_;
v___y_409_ = v___y_428_;
v___y_410_ = v___y_429_;
v___y_411_ = v___y_432_;
v___y_412_ = v___y_430_;
v___y_413_ = v___y_431_;
v___y_414_ = v_name_433_;
goto v___jp_404_;
}
case 1:
{
lean_object* v_ipv4_434_; lean_object* v___x_435_; 
v_ipv4_434_ = lean_ctor_get(v_host_423_, 0);
lean_inc_ref(v_ipv4_434_);
lean_dec_ref_known(v_host_423_, 1);
v___x_435_ = lean_uv_ntop_v4(v_ipv4_434_);
lean_dec_ref(v_ipv4_434_);
v_port_405_ = v_port_424_;
v___y_406_ = v___y_425_;
v___y_407_ = v___y_427_;
v___y_408_ = v___y_426_;
v___y_409_ = v___y_428_;
v___y_410_ = v___y_429_;
v___y_411_ = v___y_432_;
v___y_412_ = v___y_430_;
v___y_413_ = v___y_431_;
v___y_414_ = v___x_435_;
goto v___jp_404_;
}
default: 
{
lean_object* v_ipv6_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_ipv6_436_ = lean_ctor_get(v_host_423_, 0);
lean_inc_ref(v_ipv6_436_);
lean_dec_ref_known(v_host_423_, 1);
v___x_437_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_438_ = lean_uv_ntop_v6(v_ipv6_436_);
lean_dec_ref(v_ipv6_436_);
v___x_439_ = lean_string_append(v___x_437_, v___x_438_);
lean_dec_ref(v___x_438_);
v___x_440_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_441_ = lean_string_append(v___x_439_, v___x_440_);
v_port_405_ = v_port_424_;
v___y_406_ = v___y_425_;
v___y_407_ = v___y_427_;
v___y_408_ = v___y_426_;
v___y_409_ = v___y_428_;
v___y_410_ = v___y_429_;
v___y_411_ = v___y_432_;
v___y_412_ = v___y_430_;
v___y_413_ = v___y_431_;
v___y_414_ = v___x_441_;
goto v___jp_404_;
}
}
}
v___jp_442_:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_string_append(v___y_446_, v___y_444_);
lean_dec_ref(v___y_444_);
v___x_449_ = lean_string_append(v___x_448_, v___y_447_);
lean_dec_ref(v___y_447_);
v___y_327_ = v___y_443_;
v___y_328_ = v___y_445_;
v___y_329_ = v___x_449_;
goto v___jp_326_;
}
v___jp_450_:
{
switch(lean_obj_tag(v_port_452_))
{
case 0:
{
lean_object* v___x_456_; 
v___x_456_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_443_ = v___y_451_;
v___y_444_ = v___y_455_;
v___y_445_ = v___y_454_;
v___y_446_ = v___y_453_;
v___y_447_ = v___x_456_;
goto v___jp_442_;
}
case 1:
{
lean_object* v___x_457_; 
v___x_457_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_443_ = v___y_451_;
v___y_444_ = v___y_455_;
v___y_445_ = v___y_454_;
v___y_446_ = v___y_453_;
v___y_447_ = v___x_457_;
goto v___jp_442_;
}
default: 
{
uint16_t v_port_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_port_458_ = lean_ctor_get_uint16(v_port_452_, 0);
lean_dec_ref_known(v_port_452_, 0);
v___x_459_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_460_ = lean_uint16_to_nat(v_port_458_);
v___x_461_ = l_Nat_reprFast(v___x_460_);
v___x_462_ = lean_string_append(v___x_459_, v___x_461_);
lean_dec_ref(v___x_461_);
v___y_443_ = v___y_451_;
v___y_444_ = v___y_455_;
v___y_445_ = v___y_454_;
v___y_446_ = v___y_453_;
v___y_447_ = v___x_462_;
goto v___jp_442_;
}
}
}
v___jp_463_:
{
switch(lean_obj_tag(v_host_465_))
{
case 0:
{
lean_object* v_name_469_; 
v_name_469_ = lean_ctor_get(v_host_465_, 0);
lean_inc_ref(v_name_469_);
lean_dec_ref_known(v_host_465_, 1);
v___y_451_ = v___y_464_;
v_port_452_ = v_port_466_;
v___y_453_ = v___y_468_;
v___y_454_ = v___y_467_;
v___y_455_ = v_name_469_;
goto v___jp_450_;
}
case 1:
{
lean_object* v_ipv4_470_; lean_object* v___x_471_; 
v_ipv4_470_ = lean_ctor_get(v_host_465_, 0);
lean_inc_ref(v_ipv4_470_);
lean_dec_ref_known(v_host_465_, 1);
v___x_471_ = lean_uv_ntop_v4(v_ipv4_470_);
lean_dec_ref(v_ipv4_470_);
v___y_451_ = v___y_464_;
v_port_452_ = v_port_466_;
v___y_453_ = v___y_468_;
v___y_454_ = v___y_467_;
v___y_455_ = v___x_471_;
goto v___jp_450_;
}
default: 
{
lean_object* v_ipv6_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_ipv6_472_ = lean_ctor_get(v_host_465_, 0);
lean_inc_ref(v_ipv6_472_);
lean_dec_ref_known(v_host_465_, 1);
v___x_473_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_474_ = lean_uv_ntop_v6(v_ipv6_472_);
lean_dec_ref(v_ipv6_472_);
v___x_475_ = lean_string_append(v___x_473_, v___x_474_);
lean_dec_ref(v___x_474_);
v___x_476_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_477_ = lean_string_append(v___x_475_, v___x_476_);
v___y_451_ = v___y_464_;
v_port_452_ = v_port_466_;
v___y_453_ = v___y_468_;
v___y_454_ = v___y_467_;
v___y_455_ = v___x_477_;
goto v___jp_450_;
}
}
}
v___jp_478_:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__20));
lean_inc_ref(v___y_479_);
v___x_481_ = lean_string_append(v___y_479_, v___x_480_);
switch(lean_obj_tag(v_uri_310_))
{
case 0:
{
lean_object* v_path_482_; lean_object* v_query_483_; lean_object* v_segments_484_; uint8_t v_absolute_485_; lean_object* v___x_486_; lean_object* v___x_487_; size_t v_sz_488_; size_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v_result_492_; 
lean_dec_ref(v___f_305_);
v_path_482_ = lean_ctor_get(v_uri_310_, 0);
lean_inc_ref(v_path_482_);
v_query_483_ = lean_ctor_get(v_uri_310_, 1);
lean_inc(v_query_483_);
lean_dec_ref_known(v_uri_310_, 2);
v_segments_484_ = lean_ctor_get(v_path_482_, 0);
lean_inc_ref(v_segments_484_);
v_absolute_485_ = lean_ctor_get_uint8(v_path_482_, sizeof(void*)*1);
lean_dec_ref(v_path_482_);
v___x_486_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_487_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_488_ = lean_array_size(v_segments_484_);
v___x_489_ = ((size_t)0ULL);
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_487_, v___f_306_, v_sz_488_, v___x_489_, v_segments_484_);
v___x_491_ = lean_array_to_list(v___x_490_);
v_result_492_ = l_String_intercalate(v___x_486_, v___x_491_);
if (v_absolute_485_ == 0)
{
v___y_337_ = v___x_480_;
v___y_338_ = v_query_483_;
v___y_339_ = v___x_481_;
v___y_340_ = v_result_492_;
goto v___jp_336_;
}
else
{
lean_object* v___x_493_; 
v___x_493_ = lean_string_append(v___x_486_, v_result_492_);
lean_dec_ref(v_result_492_);
v___y_337_ = v___x_480_;
v___y_338_ = v_query_483_;
v___y_339_ = v___x_481_;
v___y_340_ = v___x_493_;
goto v___jp_336_;
}
}
case 1:
{
lean_object* v_uri_494_; lean_object* v_authority_495_; 
lean_dec_ref(v___f_306_);
v_uri_494_ = lean_ctor_get(v_uri_310_, 0);
lean_inc_ref(v_uri_494_);
lean_dec_ref_known(v_uri_310_, 1);
v_authority_495_ = lean_ctor_get(v_uri_494_, 1);
if (lean_obj_tag(v_authority_495_) == 0)
{
lean_object* v_scheme_496_; lean_object* v_path_497_; lean_object* v_query_498_; lean_object* v_fragment_499_; lean_object* v___x_500_; 
v_scheme_496_ = lean_ctor_get(v_uri_494_, 0);
lean_inc_ref(v_scheme_496_);
v_path_497_ = lean_ctor_get(v_uri_494_, 2);
lean_inc_ref(v_path_497_);
v_query_498_ = lean_ctor_get(v_uri_494_, 3);
lean_inc(v_query_498_);
v_fragment_499_ = lean_ctor_get(v_uri_494_, 4);
lean_inc(v_fragment_499_);
lean_dec_ref(v_uri_494_);
v___x_500_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_373_ = v___x_480_;
v___y_374_ = v_query_498_;
v___y_375_ = v_scheme_496_;
v___y_376_ = v_fragment_499_;
v___y_377_ = v___x_481_;
v___y_378_ = v_path_497_;
v___y_379_ = v___x_500_;
goto v___jp_372_;
}
else
{
lean_object* v_val_501_; lean_object* v_scheme_502_; lean_object* v_path_503_; lean_object* v_query_504_; lean_object* v_fragment_505_; lean_object* v_userInfo_506_; lean_object* v_host_507_; lean_object* v_port_508_; lean_object* v___x_509_; 
v_val_501_ = lean_ctor_get(v_authority_495_, 0);
lean_inc(v_val_501_);
v_scheme_502_ = lean_ctor_get(v_uri_494_, 0);
lean_inc_ref(v_scheme_502_);
v_path_503_ = lean_ctor_get(v_uri_494_, 2);
lean_inc_ref(v_path_503_);
v_query_504_ = lean_ctor_get(v_uri_494_, 3);
lean_inc(v_query_504_);
v_fragment_505_ = lean_ctor_get(v_uri_494_, 4);
lean_inc(v_fragment_505_);
lean_dec_ref(v_uri_494_);
v_userInfo_506_ = lean_ctor_get(v_val_501_, 0);
lean_inc(v_userInfo_506_);
v_host_507_ = lean_ctor_get(v_val_501_, 1);
lean_inc_ref(v_host_507_);
v_port_508_ = lean_ctor_get(v_val_501_, 2);
lean_inc(v_port_508_);
lean_dec(v_val_501_);
v___x_509_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__21));
if (lean_obj_tag(v_userInfo_506_) == 0)
{
lean_object* v___x_510_; 
v___x_510_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v_host_423_ = v_host_507_;
v_port_424_ = v_port_508_;
v___y_425_ = v___x_480_;
v___y_426_ = v_scheme_502_;
v___y_427_ = v_query_504_;
v___y_428_ = v_fragment_505_;
v___y_429_ = v___x_509_;
v___y_430_ = v___x_481_;
v___y_431_ = v_path_503_;
v___y_432_ = v___x_510_;
goto v___jp_422_;
}
else
{
lean_object* v_val_511_; lean_object* v_password_512_; 
v_val_511_ = lean_ctor_get(v_userInfo_506_, 0);
lean_inc(v_val_511_);
lean_dec_ref_known(v_userInfo_506_, 1);
v_password_512_ = lean_ctor_get(v_val_511_, 1);
if (lean_obj_tag(v_password_512_) == 0)
{
lean_object* v_username_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_username_513_ = lean_ctor_get(v_val_511_, 0);
lean_inc_ref(v_username_513_);
lean_dec(v_val_511_);
v___x_514_ = lean_string_from_utf8_unchecked(v_username_513_);
v___x_515_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_516_ = lean_string_append(v___x_514_, v___x_515_);
v_host_423_ = v_host_507_;
v_port_424_ = v_port_508_;
v___y_425_ = v___x_480_;
v___y_426_ = v_scheme_502_;
v___y_427_ = v_query_504_;
v___y_428_ = v_fragment_505_;
v___y_429_ = v___x_509_;
v___y_430_ = v___x_481_;
v___y_431_ = v_path_503_;
v___y_432_ = v___x_516_;
goto v___jp_422_;
}
else
{
lean_object* v_username_517_; lean_object* v_val_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
lean_inc_ref(v_password_512_);
v_username_517_ = lean_ctor_get(v_val_511_, 0);
lean_inc_ref(v_username_517_);
lean_dec(v_val_511_);
v_val_518_ = lean_ctor_get(v_password_512_, 0);
lean_inc(v_val_518_);
lean_dec_ref_known(v_password_512_, 1);
v___x_519_ = lean_string_from_utf8_unchecked(v_username_517_);
v___x_520_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_521_ = lean_string_append(v___x_519_, v___x_520_);
v___x_522_ = lean_string_from_utf8_unchecked(v_val_518_);
v___x_523_ = lean_string_append(v___x_521_, v___x_522_);
lean_dec_ref(v___x_522_);
v___x_524_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_525_ = lean_string_append(v___x_523_, v___x_524_);
v_host_423_ = v_host_507_;
v_port_424_ = v_port_508_;
v___y_425_ = v___x_480_;
v___y_426_ = v_scheme_502_;
v___y_427_ = v_query_504_;
v___y_428_ = v_fragment_505_;
v___y_429_ = v___x_509_;
v___y_430_ = v___x_481_;
v___y_431_ = v_path_503_;
v___y_432_ = v___x_525_;
goto v___jp_422_;
}
}
}
}
case 2:
{
lean_object* v_authority_526_; lean_object* v_userInfo_527_; 
lean_dec_ref(v___f_306_);
lean_dec_ref(v___f_305_);
v_authority_526_ = lean_ctor_get(v_uri_310_, 0);
lean_inc_ref(v_authority_526_);
lean_dec_ref_known(v_uri_310_, 1);
v_userInfo_527_ = lean_ctor_get(v_authority_526_, 0);
if (lean_obj_tag(v_userInfo_527_) == 0)
{
lean_object* v_host_528_; lean_object* v_port_529_; lean_object* v___x_530_; 
v_host_528_ = lean_ctor_get(v_authority_526_, 1);
lean_inc_ref(v_host_528_);
v_port_529_ = lean_ctor_get(v_authority_526_, 2);
lean_inc(v_port_529_);
lean_dec_ref(v_authority_526_);
v___x_530_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_464_ = v___x_480_;
v_host_465_ = v_host_528_;
v_port_466_ = v_port_529_;
v___y_467_ = v___x_481_;
v___y_468_ = v___x_530_;
goto v___jp_463_;
}
else
{
lean_object* v_val_531_; lean_object* v_password_532_; 
v_val_531_ = lean_ctor_get(v_userInfo_527_, 0);
lean_inc(v_val_531_);
v_password_532_ = lean_ctor_get(v_val_531_, 1);
if (lean_obj_tag(v_password_532_) == 0)
{
lean_object* v_host_533_; lean_object* v_port_534_; lean_object* v_username_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_host_533_ = lean_ctor_get(v_authority_526_, 1);
lean_inc_ref(v_host_533_);
v_port_534_ = lean_ctor_get(v_authority_526_, 2);
lean_inc(v_port_534_);
lean_dec_ref(v_authority_526_);
v_username_535_ = lean_ctor_get(v_val_531_, 0);
lean_inc_ref(v_username_535_);
lean_dec(v_val_531_);
v___x_536_ = lean_string_from_utf8_unchecked(v_username_535_);
v___x_537_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_538_ = lean_string_append(v___x_536_, v___x_537_);
v___y_464_ = v___x_480_;
v_host_465_ = v_host_533_;
v_port_466_ = v_port_534_;
v___y_467_ = v___x_481_;
v___y_468_ = v___x_538_;
goto v___jp_463_;
}
else
{
lean_object* v_host_539_; lean_object* v_port_540_; lean_object* v_username_541_; lean_object* v_val_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
lean_inc_ref(v_password_532_);
v_host_539_ = lean_ctor_get(v_authority_526_, 1);
lean_inc_ref(v_host_539_);
v_port_540_ = lean_ctor_get(v_authority_526_, 2);
lean_inc(v_port_540_);
lean_dec_ref(v_authority_526_);
v_username_541_ = lean_ctor_get(v_val_531_, 0);
lean_inc_ref(v_username_541_);
lean_dec(v_val_531_);
v_val_542_ = lean_ctor_get(v_password_532_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v_password_532_, 1);
v___x_543_ = lean_string_from_utf8_unchecked(v_username_541_);
v___x_544_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_545_ = lean_string_append(v___x_543_, v___x_544_);
v___x_546_ = lean_string_from_utf8_unchecked(v_val_542_);
v___x_547_ = lean_string_append(v___x_545_, v___x_546_);
lean_dec_ref(v___x_546_);
v___x_548_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_549_ = lean_string_append(v___x_547_, v___x_548_);
v___y_464_ = v___x_480_;
v_host_465_ = v_host_539_;
v_port_466_ = v_port_540_;
v___y_467_ = v___x_481_;
v___y_468_ = v___x_549_;
goto v___jp_463_;
}
}
}
default: 
{
lean_object* v___x_550_; 
lean_dec_ref(v___f_306_);
lean_dec_ref(v___f_305_);
v___x_550_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__23));
v___y_327_ = v___x_480_;
v___y_328_ = v___x_481_;
v___y_329_ = v___x_550_;
goto v___jp_326_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__0));
v___x_598_ = lean_string_to_utf8(v___x_597_);
return v___x_598_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__1(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0);
v___x_600_ = lean_byte_array_size(v___x_599_);
return v___x_600_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__11));
v___x_603_ = lean_string_to_utf8(v___x_602_);
return v___x_603_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__4(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3);
v___x_605_ = lean_byte_array_size(v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__5(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__12));
v___x_607_ = lean_string_to_utf8(v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__6(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__5, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__5_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__5);
v___x_609_ = lean_byte_array_size(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__7(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__13));
v___x_611_ = lean_string_to_utf8(v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__8(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__7, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__7_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__7);
v___x_613_ = lean_byte_array_size(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__9(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__14));
v___x_615_ = lean_string_to_utf8(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__10(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__9, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__9_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__9);
v___x_617_ = lean_byte_array_size(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2(lean_object* v___f_618_, lean_object* v___f_619_, lean_object* v_out_620_, lean_object* v_req_621_){
_start:
{
uint8_t v_method_622_; uint8_t v_version_623_; lean_object* v_uri_624_; lean_object* v_headers_625_; lean_object* v___y_627_; lean_object* v___y_639_; uint8_t v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_674_; uint8_t v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_683_; uint8_t v___y_684_; lean_object* v_port_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_697_; uint8_t v___y_698_; lean_object* v___y_699_; lean_object* v_host_700_; lean_object* v_port_701_; lean_object* v___y_702_; lean_object* v___y_713_; lean_object* v___y_714_; uint8_t v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_728_; lean_object* v___y_729_; uint8_t v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_744_; lean_object* v___y_745_; uint8_t v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_763_; lean_object* v___y_764_; uint8_t v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_778_; lean_object* v___y_779_; uint8_t v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v_port_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_797_; lean_object* v___y_798_; uint8_t v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v_host_803_; lean_object* v_port_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_818_; uint8_t v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_826_; 
v_method_622_ = lean_ctor_get_uint8(v_req_621_, sizeof(void*)*2);
v_version_623_ = lean_ctor_get_uint8(v_req_621_, sizeof(void*)*2 + 1);
v_uri_624_ = lean_ctor_get(v_req_621_, 0);
lean_inc(v_uri_624_);
v_headers_625_ = lean_ctor_get(v_req_621_, 1);
lean_inc_ref(v_headers_625_);
lean_dec_ref(v_req_621_);
switch(v_method_622_)
{
case 0:
{
lean_object* v___x_904_; 
v___x_904_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__24));
v___y_826_ = v___x_904_;
goto v___jp_825_;
}
case 1:
{
lean_object* v___x_905_; 
v___x_905_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__25));
v___y_826_ = v___x_905_;
goto v___jp_825_;
}
case 2:
{
lean_object* v___x_906_; 
v___x_906_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__26));
v___y_826_ = v___x_906_;
goto v___jp_825_;
}
case 3:
{
lean_object* v___x_907_; 
v___x_907_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__27));
v___y_826_ = v___x_907_;
goto v___jp_825_;
}
case 4:
{
lean_object* v___x_908_; 
v___x_908_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__28));
v___y_826_ = v___x_908_;
goto v___jp_825_;
}
case 5:
{
lean_object* v___x_909_; 
v___x_909_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__29));
v___y_826_ = v___x_909_;
goto v___jp_825_;
}
case 6:
{
lean_object* v___x_910_; 
v___x_910_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__30));
v___y_826_ = v___x_910_;
goto v___jp_825_;
}
case 7:
{
lean_object* v___x_911_; 
v___x_911_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__31));
v___y_826_ = v___x_911_;
goto v___jp_825_;
}
case 8:
{
lean_object* v___x_912_; 
v___x_912_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__32));
v___y_826_ = v___x_912_;
goto v___jp_825_;
}
case 9:
{
lean_object* v___x_913_; 
v___x_913_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__33));
v___y_826_ = v___x_913_;
goto v___jp_825_;
}
case 10:
{
lean_object* v___x_914_; 
v___x_914_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__34));
v___y_826_ = v___x_914_;
goto v___jp_825_;
}
case 11:
{
lean_object* v___x_915_; 
v___x_915_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__35));
v___y_826_ = v___x_915_;
goto v___jp_825_;
}
case 12:
{
lean_object* v___x_916_; 
v___x_916_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__36));
v___y_826_ = v___x_916_;
goto v___jp_825_;
}
case 13:
{
lean_object* v___x_917_; 
v___x_917_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__37));
v___y_826_ = v___x_917_;
goto v___jp_825_;
}
case 14:
{
lean_object* v___x_918_; 
v___x_918_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__38));
v___y_826_ = v___x_918_;
goto v___jp_825_;
}
case 15:
{
lean_object* v___x_919_; 
v___x_919_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__39));
v___y_826_ = v___x_919_;
goto v___jp_825_;
}
case 16:
{
lean_object* v___x_920_; 
v___x_920_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__40));
v___y_826_ = v___x_920_;
goto v___jp_825_;
}
case 17:
{
lean_object* v___x_921_; 
v___x_921_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__41));
v___y_826_ = v___x_921_;
goto v___jp_825_;
}
case 18:
{
lean_object* v___x_922_; 
v___x_922_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__42));
v___y_826_ = v___x_922_;
goto v___jp_825_;
}
case 19:
{
lean_object* v___x_923_; 
v___x_923_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__43));
v___y_826_ = v___x_923_;
goto v___jp_825_;
}
case 20:
{
lean_object* v___x_924_; 
v___x_924_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__44));
v___y_826_ = v___x_924_;
goto v___jp_825_;
}
case 21:
{
lean_object* v___x_925_; 
v___x_925_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__45));
v___y_826_ = v___x_925_;
goto v___jp_825_;
}
case 22:
{
lean_object* v___x_926_; 
v___x_926_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__46));
v___y_826_ = v___x_926_;
goto v___jp_825_;
}
case 23:
{
lean_object* v___x_927_; 
v___x_927_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__47));
v___y_826_ = v___x_927_;
goto v___jp_825_;
}
case 24:
{
lean_object* v___x_928_; 
v___x_928_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__48));
v___y_826_ = v___x_928_;
goto v___jp_825_;
}
case 25:
{
lean_object* v___x_929_; 
v___x_929_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__49));
v___y_826_ = v___x_929_;
goto v___jp_825_;
}
case 26:
{
lean_object* v___x_930_; 
v___x_930_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__50));
v___y_826_ = v___x_930_;
goto v___jp_825_;
}
case 27:
{
lean_object* v___x_931_; 
v___x_931_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__51));
v___y_826_ = v___x_931_;
goto v___jp_825_;
}
case 28:
{
lean_object* v___x_932_; 
v___x_932_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__52));
v___y_826_ = v___x_932_;
goto v___jp_825_;
}
case 29:
{
lean_object* v___x_933_; 
v___x_933_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__53));
v___y_826_ = v___x_933_;
goto v___jp_825_;
}
case 30:
{
lean_object* v___x_934_; 
v___x_934_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__54));
v___y_826_ = v___x_934_;
goto v___jp_825_;
}
case 31:
{
lean_object* v___x_935_; 
v___x_935_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__55));
v___y_826_ = v___x_935_;
goto v___jp_825_;
}
case 32:
{
lean_object* v___x_936_; 
v___x_936_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__56));
v___y_826_ = v___x_936_;
goto v___jp_825_;
}
case 33:
{
lean_object* v___x_937_; 
v___x_937_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__57));
v___y_826_ = v___x_937_;
goto v___jp_825_;
}
case 34:
{
lean_object* v___x_938_; 
v___x_938_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__58));
v___y_826_ = v___x_938_;
goto v___jp_825_;
}
case 35:
{
lean_object* v___x_939_; 
v___x_939_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__59));
v___y_826_ = v___x_939_;
goto v___jp_825_;
}
case 36:
{
lean_object* v___x_940_; 
v___x_940_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__60));
v___y_826_ = v___x_940_;
goto v___jp_825_;
}
case 37:
{
lean_object* v___x_941_; 
v___x_941_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__61));
v___y_826_ = v___x_941_;
goto v___jp_825_;
}
case 38:
{
lean_object* v___x_942_; 
v___x_942_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__62));
v___y_826_ = v___x_942_;
goto v___jp_825_;
}
default: 
{
lean_object* v___x_943_; 
v___x_943_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__63));
v___y_826_ = v___x_943_;
goto v___jp_825_;
}
}
v___jp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_628_ = lean_byte_array_size(v___y_627_);
v___x_629_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__1, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__1_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__1);
v___x_632_ = 0;
v___x_633_ = lean_byte_array_copy_slice(v___x_629_, v___x_630_, v___y_627_, v___x_628_, v___x_631_, v___x_632_);
v___x_634_ = ((lean_object*)(l_Std_Http_Request_instEncodeV11Head___lam__2___closed__2));
v___x_635_ = l_Std_Http_Headers_fold___redArg(v_headers_625_, v___x_633_, v___x_634_);
lean_dec_ref(v_headers_625_);
v___x_636_ = lean_byte_array_size(v___x_635_);
v___x_637_ = lean_byte_array_copy_slice(v___x_629_, v___x_630_, v___x_635_, v___x_636_, v___x_631_, v___x_632_);
return v___x_637_;
}
v___jp_638_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; lean_object* v___x_648_; 
v___x_643_ = lean_byte_array_size(v___y_641_);
v___x_644_ = lean_string_to_utf8(v___y_642_);
v___x_645_ = lean_byte_array_size(v___x_644_);
v___x_646_ = lean_byte_array_copy_slice(v___x_644_, v___y_639_, v___y_641_, v___x_643_, v___x_645_, v___y_640_);
lean_dec_ref(v___x_644_);
v___x_647_ = 32;
v___x_648_ = lean_byte_array_push(v___x_646_, v___x_647_);
switch(v_version_623_)
{
case 0:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; lean_object* v___x_654_; 
v___x_649_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3);
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_651_ = lean_byte_array_size(v___x_648_);
v___x_652_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__4, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__4_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__4);
v___x_653_ = 0;
v___x_654_ = lean_byte_array_copy_slice(v___x_649_, v___x_650_, v___x_648_, v___x_651_, v___x_652_, v___x_653_);
v___y_627_ = v___x_654_;
goto v___jp_626_;
}
case 1:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; lean_object* v___x_660_; 
v___x_655_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__5, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__5_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__5);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_byte_array_size(v___x_648_);
v___x_658_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__6, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__6_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__6);
v___x_659_ = 0;
v___x_660_ = lean_byte_array_copy_slice(v___x_655_, v___x_656_, v___x_648_, v___x_657_, v___x_658_, v___x_659_);
v___y_627_ = v___x_660_;
goto v___jp_626_;
}
case 2:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; 
v___x_661_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__7, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__7_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__7);
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_byte_array_size(v___x_648_);
v___x_664_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__8, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__8_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__8);
v___x_665_ = 0;
v___x_666_ = lean_byte_array_copy_slice(v___x_661_, v___x_662_, v___x_648_, v___x_663_, v___x_664_, v___x_665_);
v___y_627_ = v___x_666_;
goto v___jp_626_;
}
default: 
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; lean_object* v___x_672_; 
v___x_667_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__9, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__9_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__9);
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_byte_array_size(v___x_648_);
v___x_670_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__10, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__10_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__10);
v___x_671_ = 0;
v___x_672_ = lean_byte_array_copy_slice(v___x_667_, v___x_668_, v___x_648_, v___x_669_, v___x_670_, v___x_671_);
v___y_627_ = v___x_672_;
goto v___jp_626_;
}
}
}
v___jp_673_:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_string_append(v___y_677_, v___y_678_);
lean_dec_ref(v___y_678_);
v___x_681_ = lean_string_append(v___x_680_, v___y_679_);
lean_dec_ref(v___y_679_);
v___y_639_ = v___y_674_;
v___y_640_ = v___y_675_;
v___y_641_ = v___y_676_;
v___y_642_ = v___x_681_;
goto v___jp_638_;
}
v___jp_682_:
{
switch(lean_obj_tag(v_port_685_))
{
case 0:
{
lean_object* v___x_689_; 
v___x_689_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_674_ = v___y_683_;
v___y_675_ = v___y_684_;
v___y_676_ = v___y_687_;
v___y_677_ = v___y_686_;
v___y_678_ = v___y_688_;
v___y_679_ = v___x_689_;
goto v___jp_673_;
}
case 1:
{
lean_object* v___x_690_; 
v___x_690_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_674_ = v___y_683_;
v___y_675_ = v___y_684_;
v___y_676_ = v___y_687_;
v___y_677_ = v___y_686_;
v___y_678_ = v___y_688_;
v___y_679_ = v___x_690_;
goto v___jp_673_;
}
default: 
{
uint16_t v_port_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_port_691_ = lean_ctor_get_uint16(v_port_685_, 0);
lean_dec_ref_known(v_port_685_, 0);
v___x_692_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_693_ = lean_uint16_to_nat(v_port_691_);
v___x_694_ = l_Nat_reprFast(v___x_693_);
v___x_695_ = lean_string_append(v___x_692_, v___x_694_);
lean_dec_ref(v___x_694_);
v___y_674_ = v___y_683_;
v___y_675_ = v___y_684_;
v___y_676_ = v___y_687_;
v___y_677_ = v___y_686_;
v___y_678_ = v___y_688_;
v___y_679_ = v___x_695_;
goto v___jp_673_;
}
}
}
v___jp_696_:
{
switch(lean_obj_tag(v_host_700_))
{
case 0:
{
lean_object* v_name_703_; 
v_name_703_ = lean_ctor_get(v_host_700_, 0);
lean_inc_ref(v_name_703_);
lean_dec_ref_known(v_host_700_, 1);
v___y_683_ = v___y_697_;
v___y_684_ = v___y_698_;
v_port_685_ = v_port_701_;
v___y_686_ = v___y_702_;
v___y_687_ = v___y_699_;
v___y_688_ = v_name_703_;
goto v___jp_682_;
}
case 1:
{
lean_object* v_ipv4_704_; lean_object* v___x_705_; 
v_ipv4_704_ = lean_ctor_get(v_host_700_, 0);
lean_inc_ref(v_ipv4_704_);
lean_dec_ref_known(v_host_700_, 1);
v___x_705_ = lean_uv_ntop_v4(v_ipv4_704_);
lean_dec_ref(v_ipv4_704_);
v___y_683_ = v___y_697_;
v___y_684_ = v___y_698_;
v_port_685_ = v_port_701_;
v___y_686_ = v___y_702_;
v___y_687_ = v___y_699_;
v___y_688_ = v___x_705_;
goto v___jp_682_;
}
default: 
{
lean_object* v_ipv6_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_ipv6_706_ = lean_ctor_get(v_host_700_, 0);
lean_inc_ref(v_ipv6_706_);
lean_dec_ref_known(v_host_700_, 1);
v___x_707_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_708_ = lean_uv_ntop_v6(v_ipv6_706_);
lean_dec_ref(v_ipv6_706_);
v___x_709_ = lean_string_append(v___x_707_, v___x_708_);
lean_dec_ref(v___x_708_);
v___x_710_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_711_ = lean_string_append(v___x_709_, v___x_710_);
v___y_683_ = v___y_697_;
v___y_684_ = v___y_698_;
v_port_685_ = v_port_701_;
v___y_686_ = v___y_702_;
v___y_687_ = v___y_699_;
v___y_688_ = v___x_711_;
goto v___jp_682_;
}
}
}
v___jp_712_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_721_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_722_ = lean_string_append(v___y_714_, v___x_721_);
v___x_723_ = lean_string_append(v___x_722_, v___y_718_);
lean_dec_ref(v___y_718_);
v___x_724_ = lean_string_append(v___x_723_, v___y_719_);
lean_dec_ref(v___y_719_);
v___x_725_ = lean_string_append(v___x_724_, v___y_717_);
lean_dec_ref(v___y_717_);
v___x_726_ = lean_string_append(v___x_725_, v___y_720_);
lean_dec_ref(v___y_720_);
v___y_639_ = v___y_713_;
v___y_640_ = v___y_715_;
v___y_641_ = v___y_716_;
v___y_642_ = v___x_726_;
goto v___jp_638_;
}
v___jp_727_:
{
lean_object* v_queryPart_736_; 
v_queryPart_736_ = l_Std_Http_URI_Query_formatOption(v___y_732_);
if (lean_obj_tag(v___y_733_) == 0)
{
lean_object* v___x_737_; 
v___x_737_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_713_ = v___y_729_;
v___y_714_ = v___y_728_;
v___y_715_ = v___y_730_;
v___y_716_ = v___y_731_;
v___y_717_ = v_queryPart_736_;
v___y_718_ = v___y_734_;
v___y_719_ = v___y_735_;
v___y_720_ = v___x_737_;
goto v___jp_712_;
}
else
{
lean_object* v_val_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_val_738_ = lean_ctor_get(v___y_733_, 0);
lean_inc(v_val_738_);
lean_dec_ref_known(v___y_733_, 1);
v___x_739_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__16));
v___x_740_ = l_Std_Http_URI_EncodedFragment_encode(v_val_738_);
v___x_741_ = lean_string_from_utf8_unchecked(v___x_740_);
v___x_742_ = lean_string_append(v___x_739_, v___x_741_);
lean_dec_ref(v___x_741_);
v___y_713_ = v___y_729_;
v___y_714_ = v___y_728_;
v___y_715_ = v___y_730_;
v___y_716_ = v___y_731_;
v___y_717_ = v_queryPart_736_;
v___y_718_ = v___y_734_;
v___y_719_ = v___y_735_;
v___y_720_ = v___x_742_;
goto v___jp_712_;
}
}
v___jp_743_:
{
lean_object* v_segments_752_; uint8_t v_absolute_753_; lean_object* v___x_754_; lean_object* v___x_755_; size_t v_sz_756_; size_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v_result_760_; 
v_segments_752_ = lean_ctor_get(v___y_749_, 0);
lean_inc_ref(v_segments_752_);
v_absolute_753_ = lean_ctor_get_uint8(v___y_749_, sizeof(void*)*1);
lean_dec_ref(v___y_749_);
v___x_754_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_755_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_756_ = lean_array_size(v_segments_752_);
v___x_757_ = ((size_t)0ULL);
v___x_758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_755_, v___f_618_, v_sz_756_, v___x_757_, v_segments_752_);
v___x_759_ = lean_array_to_list(v___x_758_);
v_result_760_ = l_String_intercalate(v___x_754_, v___x_759_);
if (v_absolute_753_ == 0)
{
v___y_728_ = v___y_745_;
v___y_729_ = v___y_744_;
v___y_730_ = v___y_746_;
v___y_731_ = v___y_748_;
v___y_732_ = v___y_747_;
v___y_733_ = v___y_750_;
v___y_734_ = v___y_751_;
v___y_735_ = v_result_760_;
goto v___jp_727_;
}
else
{
lean_object* v___x_761_; 
v___x_761_ = lean_string_append(v___x_754_, v_result_760_);
lean_dec_ref(v_result_760_);
v___y_728_ = v___y_745_;
v___y_729_ = v___y_744_;
v___y_730_ = v___y_746_;
v___y_731_ = v___y_748_;
v___y_732_ = v___y_747_;
v___y_733_ = v___y_750_;
v___y_734_ = v___y_751_;
v___y_735_ = v___x_761_;
goto v___jp_727_;
}
}
v___jp_762_:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_string_append(v___y_766_, v___y_770_);
lean_dec_ref(v___y_770_);
v___x_775_ = lean_string_append(v___x_774_, v___y_773_);
lean_dec_ref(v___y_773_);
lean_inc_ref(v___y_769_);
v___x_776_ = lean_string_append(v___y_769_, v___x_775_);
lean_dec_ref(v___x_775_);
v___y_744_ = v___y_764_;
v___y_745_ = v___y_763_;
v___y_746_ = v___y_765_;
v___y_747_ = v___y_768_;
v___y_748_ = v___y_767_;
v___y_749_ = v___y_771_;
v___y_750_ = v___y_772_;
v___y_751_ = v___x_776_;
goto v___jp_743_;
}
v___jp_777_:
{
switch(lean_obj_tag(v_port_784_))
{
case 0:
{
lean_object* v___x_789_; 
v___x_789_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_763_ = v___y_779_;
v___y_764_ = v___y_778_;
v___y_765_ = v___y_780_;
v___y_766_ = v___y_781_;
v___y_767_ = v___y_783_;
v___y_768_ = v___y_782_;
v___y_769_ = v___y_785_;
v___y_770_ = v___y_788_;
v___y_771_ = v___y_786_;
v___y_772_ = v___y_787_;
v___y_773_ = v___x_789_;
goto v___jp_762_;
}
case 1:
{
lean_object* v___x_790_; 
v___x_790_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_763_ = v___y_779_;
v___y_764_ = v___y_778_;
v___y_765_ = v___y_780_;
v___y_766_ = v___y_781_;
v___y_767_ = v___y_783_;
v___y_768_ = v___y_782_;
v___y_769_ = v___y_785_;
v___y_770_ = v___y_788_;
v___y_771_ = v___y_786_;
v___y_772_ = v___y_787_;
v___y_773_ = v___x_790_;
goto v___jp_762_;
}
default: 
{
uint16_t v_port_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_port_791_ = lean_ctor_get_uint16(v_port_784_, 0);
lean_dec_ref_known(v_port_784_, 0);
v___x_792_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_793_ = lean_uint16_to_nat(v_port_791_);
v___x_794_ = l_Nat_reprFast(v___x_793_);
v___x_795_ = lean_string_append(v___x_792_, v___x_794_);
lean_dec_ref(v___x_794_);
v___y_763_ = v___y_779_;
v___y_764_ = v___y_778_;
v___y_765_ = v___y_780_;
v___y_766_ = v___y_781_;
v___y_767_ = v___y_783_;
v___y_768_ = v___y_782_;
v___y_769_ = v___y_785_;
v___y_770_ = v___y_788_;
v___y_771_ = v___y_786_;
v___y_772_ = v___y_787_;
v___y_773_ = v___x_795_;
goto v___jp_762_;
}
}
}
v___jp_796_:
{
switch(lean_obj_tag(v_host_803_))
{
case 0:
{
lean_object* v_name_808_; 
v_name_808_ = lean_ctor_get(v_host_803_, 0);
lean_inc_ref(v_name_808_);
lean_dec_ref_known(v_host_803_, 1);
v___y_778_ = v___y_798_;
v___y_779_ = v___y_797_;
v___y_780_ = v___y_799_;
v___y_781_ = v___y_807_;
v___y_782_ = v___y_801_;
v___y_783_ = v___y_800_;
v_port_784_ = v_port_804_;
v___y_785_ = v___y_802_;
v___y_786_ = v___y_805_;
v___y_787_ = v___y_806_;
v___y_788_ = v_name_808_;
goto v___jp_777_;
}
case 1:
{
lean_object* v_ipv4_809_; lean_object* v___x_810_; 
v_ipv4_809_ = lean_ctor_get(v_host_803_, 0);
lean_inc_ref(v_ipv4_809_);
lean_dec_ref_known(v_host_803_, 1);
v___x_810_ = lean_uv_ntop_v4(v_ipv4_809_);
lean_dec_ref(v_ipv4_809_);
v___y_778_ = v___y_798_;
v___y_779_ = v___y_797_;
v___y_780_ = v___y_799_;
v___y_781_ = v___y_807_;
v___y_782_ = v___y_801_;
v___y_783_ = v___y_800_;
v_port_784_ = v_port_804_;
v___y_785_ = v___y_802_;
v___y_786_ = v___y_805_;
v___y_787_ = v___y_806_;
v___y_788_ = v___x_810_;
goto v___jp_777_;
}
default: 
{
lean_object* v_ipv6_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_ipv6_811_ = lean_ctor_get(v_host_803_, 0);
lean_inc_ref(v_ipv6_811_);
lean_dec_ref_known(v_host_803_, 1);
v___x_812_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_813_ = lean_uv_ntop_v6(v_ipv6_811_);
lean_dec_ref(v_ipv6_811_);
v___x_814_ = lean_string_append(v___x_812_, v___x_813_);
lean_dec_ref(v___x_813_);
v___x_815_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_816_ = lean_string_append(v___x_814_, v___x_815_);
v___y_778_ = v___y_798_;
v___y_779_ = v___y_797_;
v___y_780_ = v___y_799_;
v___y_781_ = v___y_807_;
v___y_782_ = v___y_801_;
v___y_783_ = v___y_800_;
v_port_784_ = v_port_804_;
v___y_785_ = v___y_802_;
v___y_786_ = v___y_805_;
v___y_787_ = v___y_806_;
v___y_788_ = v___x_816_;
goto v___jp_777_;
}
}
}
v___jp_817_:
{
lean_object* v_queryStr_823_; lean_object* v___x_824_; 
v_queryStr_823_ = l_Std_Http_URI_Query_formatOption(v___y_821_);
v___x_824_ = lean_string_append(v___y_822_, v_queryStr_823_);
lean_dec_ref(v_queryStr_823_);
v___y_639_ = v___y_818_;
v___y_640_ = v___y_819_;
v___y_641_ = v___y_820_;
v___y_642_ = v___x_824_;
goto v___jp_638_;
}
v___jp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; lean_object* v___x_834_; 
v___x_827_ = lean_byte_array_size(v_out_620_);
lean_inc_ref(v___y_826_);
v___x_828_ = lean_string_to_utf8(v___y_826_);
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_byte_array_size(v___x_828_);
v___x_831_ = 0;
v___x_832_ = lean_byte_array_copy_slice(v___x_828_, v___x_829_, v_out_620_, v___x_827_, v___x_830_, v___x_831_);
lean_dec_ref(v___x_828_);
v___x_833_ = 32;
v___x_834_ = lean_byte_array_push(v___x_832_, v___x_833_);
switch(lean_obj_tag(v_uri_624_))
{
case 0:
{
lean_object* v_path_835_; lean_object* v_query_836_; lean_object* v_segments_837_; uint8_t v_absolute_838_; lean_object* v___x_839_; lean_object* v___x_840_; size_t v_sz_841_; size_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v_result_845_; 
lean_dec_ref(v___f_618_);
v_path_835_ = lean_ctor_get(v_uri_624_, 0);
lean_inc_ref(v_path_835_);
v_query_836_ = lean_ctor_get(v_uri_624_, 1);
lean_inc(v_query_836_);
lean_dec_ref_known(v_uri_624_, 2);
v_segments_837_ = lean_ctor_get(v_path_835_, 0);
lean_inc_ref(v_segments_837_);
v_absolute_838_ = lean_ctor_get_uint8(v_path_835_, sizeof(void*)*1);
lean_dec_ref(v_path_835_);
v___x_839_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_840_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_841_ = lean_array_size(v_segments_837_);
v___x_842_ = ((size_t)0ULL);
v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_840_, v___f_619_, v_sz_841_, v___x_842_, v_segments_837_);
v___x_844_ = lean_array_to_list(v___x_843_);
v_result_845_ = l_String_intercalate(v___x_839_, v___x_844_);
if (v_absolute_838_ == 0)
{
v___y_818_ = v___x_829_;
v___y_819_ = v___x_831_;
v___y_820_ = v___x_834_;
v___y_821_ = v_query_836_;
v___y_822_ = v_result_845_;
goto v___jp_817_;
}
else
{
lean_object* v___x_846_; 
v___x_846_ = lean_string_append(v___x_839_, v_result_845_);
lean_dec_ref(v_result_845_);
v___y_818_ = v___x_829_;
v___y_819_ = v___x_831_;
v___y_820_ = v___x_834_;
v___y_821_ = v_query_836_;
v___y_822_ = v___x_846_;
goto v___jp_817_;
}
}
case 1:
{
lean_object* v_uri_847_; lean_object* v_authority_848_; 
lean_dec_ref(v___f_619_);
v_uri_847_ = lean_ctor_get(v_uri_624_, 0);
lean_inc_ref(v_uri_847_);
lean_dec_ref_known(v_uri_624_, 1);
v_authority_848_ = lean_ctor_get(v_uri_847_, 1);
if (lean_obj_tag(v_authority_848_) == 0)
{
lean_object* v_scheme_849_; lean_object* v_path_850_; lean_object* v_query_851_; lean_object* v_fragment_852_; lean_object* v___x_853_; 
v_scheme_849_ = lean_ctor_get(v_uri_847_, 0);
lean_inc_ref(v_scheme_849_);
v_path_850_ = lean_ctor_get(v_uri_847_, 2);
lean_inc_ref(v_path_850_);
v_query_851_ = lean_ctor_get(v_uri_847_, 3);
lean_inc(v_query_851_);
v_fragment_852_ = lean_ctor_get(v_uri_847_, 4);
lean_inc(v_fragment_852_);
lean_dec_ref(v_uri_847_);
v___x_853_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_744_ = v___x_829_;
v___y_745_ = v_scheme_849_;
v___y_746_ = v___x_831_;
v___y_747_ = v_query_851_;
v___y_748_ = v___x_834_;
v___y_749_ = v_path_850_;
v___y_750_ = v_fragment_852_;
v___y_751_ = v___x_853_;
goto v___jp_743_;
}
else
{
lean_object* v_val_854_; lean_object* v_scheme_855_; lean_object* v_path_856_; lean_object* v_query_857_; lean_object* v_fragment_858_; lean_object* v_userInfo_859_; lean_object* v_host_860_; lean_object* v_port_861_; lean_object* v___x_862_; 
v_val_854_ = lean_ctor_get(v_authority_848_, 0);
lean_inc(v_val_854_);
v_scheme_855_ = lean_ctor_get(v_uri_847_, 0);
lean_inc_ref(v_scheme_855_);
v_path_856_ = lean_ctor_get(v_uri_847_, 2);
lean_inc_ref(v_path_856_);
v_query_857_ = lean_ctor_get(v_uri_847_, 3);
lean_inc(v_query_857_);
v_fragment_858_ = lean_ctor_get(v_uri_847_, 4);
lean_inc(v_fragment_858_);
lean_dec_ref(v_uri_847_);
v_userInfo_859_ = lean_ctor_get(v_val_854_, 0);
lean_inc(v_userInfo_859_);
v_host_860_ = lean_ctor_get(v_val_854_, 1);
lean_inc_ref(v_host_860_);
v_port_861_ = lean_ctor_get(v_val_854_, 2);
lean_inc(v_port_861_);
lean_dec(v_val_854_);
v___x_862_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__21));
if (lean_obj_tag(v_userInfo_859_) == 0)
{
lean_object* v___x_863_; 
v___x_863_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_797_ = v_scheme_855_;
v___y_798_ = v___x_829_;
v___y_799_ = v___x_831_;
v___y_800_ = v___x_834_;
v___y_801_ = v_query_857_;
v___y_802_ = v___x_862_;
v_host_803_ = v_host_860_;
v_port_804_ = v_port_861_;
v___y_805_ = v_path_856_;
v___y_806_ = v_fragment_858_;
v___y_807_ = v___x_863_;
goto v___jp_796_;
}
else
{
lean_object* v_val_864_; lean_object* v_password_865_; 
v_val_864_ = lean_ctor_get(v_userInfo_859_, 0);
lean_inc(v_val_864_);
lean_dec_ref_known(v_userInfo_859_, 1);
v_password_865_ = lean_ctor_get(v_val_864_, 1);
if (lean_obj_tag(v_password_865_) == 0)
{
lean_object* v_username_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_username_866_ = lean_ctor_get(v_val_864_, 0);
lean_inc_ref(v_username_866_);
lean_dec(v_val_864_);
v___x_867_ = lean_string_from_utf8_unchecked(v_username_866_);
v___x_868_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_869_ = lean_string_append(v___x_867_, v___x_868_);
v___y_797_ = v_scheme_855_;
v___y_798_ = v___x_829_;
v___y_799_ = v___x_831_;
v___y_800_ = v___x_834_;
v___y_801_ = v_query_857_;
v___y_802_ = v___x_862_;
v_host_803_ = v_host_860_;
v_port_804_ = v_port_861_;
v___y_805_ = v_path_856_;
v___y_806_ = v_fragment_858_;
v___y_807_ = v___x_869_;
goto v___jp_796_;
}
else
{
lean_object* v_username_870_; lean_object* v_val_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
lean_inc_ref(v_password_865_);
v_username_870_ = lean_ctor_get(v_val_864_, 0);
lean_inc_ref(v_username_870_);
lean_dec(v_val_864_);
v_val_871_ = lean_ctor_get(v_password_865_, 0);
lean_inc(v_val_871_);
lean_dec_ref_known(v_password_865_, 1);
v___x_872_ = lean_string_from_utf8_unchecked(v_username_870_);
v___x_873_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_874_ = lean_string_append(v___x_872_, v___x_873_);
v___x_875_ = lean_string_from_utf8_unchecked(v_val_871_);
v___x_876_ = lean_string_append(v___x_874_, v___x_875_);
lean_dec_ref(v___x_875_);
v___x_877_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_878_ = lean_string_append(v___x_876_, v___x_877_);
v___y_797_ = v_scheme_855_;
v___y_798_ = v___x_829_;
v___y_799_ = v___x_831_;
v___y_800_ = v___x_834_;
v___y_801_ = v_query_857_;
v___y_802_ = v___x_862_;
v_host_803_ = v_host_860_;
v_port_804_ = v_port_861_;
v___y_805_ = v_path_856_;
v___y_806_ = v_fragment_858_;
v___y_807_ = v___x_878_;
goto v___jp_796_;
}
}
}
}
case 2:
{
lean_object* v_authority_879_; lean_object* v_userInfo_880_; 
lean_dec_ref(v___f_619_);
lean_dec_ref(v___f_618_);
v_authority_879_ = lean_ctor_get(v_uri_624_, 0);
lean_inc_ref(v_authority_879_);
lean_dec_ref_known(v_uri_624_, 1);
v_userInfo_880_ = lean_ctor_get(v_authority_879_, 0);
if (lean_obj_tag(v_userInfo_880_) == 0)
{
lean_object* v_host_881_; lean_object* v_port_882_; lean_object* v___x_883_; 
v_host_881_ = lean_ctor_get(v_authority_879_, 1);
lean_inc_ref(v_host_881_);
v_port_882_ = lean_ctor_get(v_authority_879_, 2);
lean_inc(v_port_882_);
lean_dec_ref(v_authority_879_);
v___x_883_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_697_ = v___x_829_;
v___y_698_ = v___x_831_;
v___y_699_ = v___x_834_;
v_host_700_ = v_host_881_;
v_port_701_ = v_port_882_;
v___y_702_ = v___x_883_;
goto v___jp_696_;
}
else
{
lean_object* v_val_884_; lean_object* v_password_885_; 
v_val_884_ = lean_ctor_get(v_userInfo_880_, 0);
lean_inc(v_val_884_);
v_password_885_ = lean_ctor_get(v_val_884_, 1);
if (lean_obj_tag(v_password_885_) == 0)
{
lean_object* v_host_886_; lean_object* v_port_887_; lean_object* v_username_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_host_886_ = lean_ctor_get(v_authority_879_, 1);
lean_inc_ref(v_host_886_);
v_port_887_ = lean_ctor_get(v_authority_879_, 2);
lean_inc(v_port_887_);
lean_dec_ref(v_authority_879_);
v_username_888_ = lean_ctor_get(v_val_884_, 0);
lean_inc_ref(v_username_888_);
lean_dec(v_val_884_);
v___x_889_ = lean_string_from_utf8_unchecked(v_username_888_);
v___x_890_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_891_ = lean_string_append(v___x_889_, v___x_890_);
v___y_697_ = v___x_829_;
v___y_698_ = v___x_831_;
v___y_699_ = v___x_834_;
v_host_700_ = v_host_886_;
v_port_701_ = v_port_887_;
v___y_702_ = v___x_891_;
goto v___jp_696_;
}
else
{
lean_object* v_host_892_; lean_object* v_port_893_; lean_object* v_username_894_; lean_object* v_val_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
lean_inc_ref(v_password_885_);
v_host_892_ = lean_ctor_get(v_authority_879_, 1);
lean_inc_ref(v_host_892_);
v_port_893_ = lean_ctor_get(v_authority_879_, 2);
lean_inc(v_port_893_);
lean_dec_ref(v_authority_879_);
v_username_894_ = lean_ctor_get(v_val_884_, 0);
lean_inc_ref(v_username_894_);
lean_dec(v_val_884_);
v_val_895_ = lean_ctor_get(v_password_885_, 0);
lean_inc(v_val_895_);
lean_dec_ref_known(v_password_885_, 1);
v___x_896_ = lean_string_from_utf8_unchecked(v_username_894_);
v___x_897_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_898_ = lean_string_append(v___x_896_, v___x_897_);
v___x_899_ = lean_string_from_utf8_unchecked(v_val_895_);
v___x_900_ = lean_string_append(v___x_898_, v___x_899_);
lean_dec_ref(v___x_899_);
v___x_901_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_902_ = lean_string_append(v___x_900_, v___x_901_);
v___y_697_ = v___x_829_;
v___y_698_ = v___x_831_;
v___y_699_ = v___x_834_;
v_host_700_ = v_host_892_;
v_port_701_ = v_port_893_;
v___y_702_ = v___x_902_;
goto v___jp_696_;
}
}
}
default: 
{
lean_object* v___x_903_; 
lean_dec_ref(v___f_619_);
lean_dec_ref(v___f_618_);
v___x_903_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__23));
v___y_639_ = v___x_829_;
v___y_640_ = v___x_831_;
v___y_641_ = v___x_834_;
v___y_642_ = v___x_903_;
goto v___jp_638_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__0(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; uint8_t v___x_950_; lean_object* v___x_951_; 
v___x_947_ = l_Std_Http_Headers_empty;
v___x_948_ = lean_box(3);
v___x_949_ = 1;
v___x_950_ = 8;
v___x_951_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_951_, 0, v___x_948_);
lean_ctor_set(v___x_951_, 1, v___x_947_);
lean_ctor_set_uint8(v___x_951_, sizeof(void*)*2, v___x_950_);
lean_ctor_set_uint8(v___x_951_, sizeof(void*)*2 + 1, v___x_949_);
return v___x_951_;
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__1(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = l_Std_Http_Extensions_empty;
v___x_953_ = lean_obj_once(&l_Std_Http_Request_new___closed__0, &l_Std_Http_Request_new___closed__0_once, _init_l_Std_Http_Request_new___closed__0);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
lean_ctor_set(v___x_954_, 1, v___x_952_);
return v___x_954_;
}
}
static lean_object* _init_l_Std_Http_Request_new(void){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = lean_obj_once(&l_Std_Http_Request_new___closed__1, &l_Std_Http_Request_new___closed__1_once, _init_l_Std_Http_Request_new___closed__1);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method(lean_object* v_builder_956_, uint8_t v_method_957_){
_start:
{
lean_object* v_line_958_; lean_object* v_extensions_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_976_; 
v_line_958_ = lean_ctor_get(v_builder_956_, 0);
v_extensions_959_ = lean_ctor_get(v_builder_956_, 1);
v_isSharedCheck_976_ = !lean_is_exclusive(v_builder_956_);
if (v_isSharedCheck_976_ == 0)
{
v___x_961_ = v_builder_956_;
v_isShared_962_ = v_isSharedCheck_976_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_extensions_959_);
lean_inc(v_line_958_);
lean_dec(v_builder_956_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_976_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
uint8_t v_version_963_; lean_object* v_uri_964_; lean_object* v_headers_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_975_; 
v_version_963_ = lean_ctor_get_uint8(v_line_958_, sizeof(void*)*2 + 1);
v_uri_964_ = lean_ctor_get(v_line_958_, 0);
v_headers_965_ = lean_ctor_get(v_line_958_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_line_958_);
if (v_isSharedCheck_975_ == 0)
{
v___x_967_ = v_line_958_;
v_isShared_968_ = v_isSharedCheck_975_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_headers_965_);
lean_inc(v_uri_964_);
lean_dec(v_line_958_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_975_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_uri_964_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_headers_965_);
lean_ctor_set_uint8(v_reuseFailAlloc_974_, sizeof(void*)*2 + 1, v_version_963_);
v___x_970_ = v_reuseFailAlloc_974_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_972_; 
lean_ctor_set_uint8(v___x_970_, sizeof(void*)*2, v_method_957_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_970_);
v___x_972_ = v___x_961_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_extensions_959_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method___boxed(lean_object* v_builder_977_, lean_object* v_method_978_){
_start:
{
uint8_t v_method_boxed_979_; lean_object* v_res_980_; 
v_method_boxed_979_ = lean_unbox(v_method_978_);
v_res_980_ = l_Std_Http_Request_Builder_method(v_builder_977_, v_method_boxed_979_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version(lean_object* v_builder_981_, uint8_t v_version_982_){
_start:
{
lean_object* v_line_983_; lean_object* v_extensions_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1001_; 
v_line_983_ = lean_ctor_get(v_builder_981_, 0);
v_extensions_984_ = lean_ctor_get(v_builder_981_, 1);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_builder_981_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_986_ = v_builder_981_;
v_isShared_987_ = v_isSharedCheck_1001_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_extensions_984_);
lean_inc(v_line_983_);
lean_dec(v_builder_981_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1001_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
uint8_t v_method_988_; lean_object* v_uri_989_; lean_object* v_headers_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1000_; 
v_method_988_ = lean_ctor_get_uint8(v_line_983_, sizeof(void*)*2);
v_uri_989_ = lean_ctor_get(v_line_983_, 0);
v_headers_990_ = lean_ctor_get(v_line_983_, 1);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_line_983_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_992_ = v_line_983_;
v_isShared_993_ = v_isSharedCheck_1000_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_headers_990_);
lean_inc(v_uri_989_);
lean_dec(v_line_983_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1000_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_uri_989_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_headers_990_);
lean_ctor_set_uint8(v_reuseFailAlloc_999_, sizeof(void*)*2, v_method_988_);
v___x_995_ = v_reuseFailAlloc_999_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_997_; 
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*2 + 1, v_version_982_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_995_);
v___x_997_ = v___x_986_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_extensions_984_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version___boxed(lean_object* v_builder_1002_, lean_object* v_version_1003_){
_start:
{
uint8_t v_version_boxed_1004_; lean_object* v_res_1005_; 
v_version_boxed_1004_ = lean_unbox(v_version_1003_);
v_res_1005_ = l_Std_Http_Request_Builder_version(v_builder_1002_, v_version_boxed_1004_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri(lean_object* v_builder_1006_, lean_object* v_uri_1007_){
_start:
{
lean_object* v_line_1008_; lean_object* v_extensions_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1027_; 
v_line_1008_ = lean_ctor_get(v_builder_1006_, 0);
v_extensions_1009_ = lean_ctor_get(v_builder_1006_, 1);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_builder_1006_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1011_ = v_builder_1006_;
v_isShared_1012_ = v_isSharedCheck_1027_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_extensions_1009_);
lean_inc(v_line_1008_);
lean_dec(v_builder_1006_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1027_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
uint8_t v_method_1013_; uint8_t v_version_1014_; lean_object* v_headers_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1025_; 
v_method_1013_ = lean_ctor_get_uint8(v_line_1008_, sizeof(void*)*2);
v_version_1014_ = lean_ctor_get_uint8(v_line_1008_, sizeof(void*)*2 + 1);
v_headers_1015_ = lean_ctor_get(v_line_1008_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_line_1008_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v_line_1008_, 0);
lean_dec(v_unused_1026_);
v___x_1017_ = v_line_1008_;
v_isShared_1018_ = v_isSharedCheck_1025_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_headers_1015_);
lean_dec(v_line_1008_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1025_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v_uri_1007_);
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_uri_1007_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_headers_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1024_, sizeof(void*)*2, v_method_1013_);
lean_ctor_set_uint8(v_reuseFailAlloc_1024_, sizeof(void*)*2 + 1, v_version_1014_);
v___x_1020_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1022_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1020_);
v___x_1022_ = v___x_1011_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_extensions_1009_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(lean_object* v_msg_1028_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = l_Std_Http_instInhabitedRequestTarget_default;
v___x_1030_ = lean_panic_fn_borrowed(v___x_1029_, v_msg_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___lam__0(lean_object* v___x_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_pos_1037_; lean_object* v_array_1038_; lean_object* v_idx_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v_pos_1037_ = lean_ctor_get(v___x_1036_, 0);
v_array_1038_ = lean_ctor_get(v_pos_1037_, 0);
v_idx_1039_ = lean_ctor_get(v_pos_1037_, 1);
v___x_1040_ = lean_byte_array_size(v_array_1038_);
v___x_1041_ = lean_nat_dec_lt(v_idx_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
return v___x_1036_;
}
else
{
lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1049_; 
lean_inc(v_pos_1037_);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1049_ == 0)
{
lean_object* v_unused_1050_; lean_object* v_unused_1051_; 
v_unused_1050_ = lean_ctor_get(v___x_1036_, 1);
lean_dec(v_unused_1050_);
v_unused_1051_ = lean_ctor_get(v___x_1036_, 0);
lean_dec(v_unused_1051_);
v___x_1043_ = v___x_1036_;
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
else
{
lean_dec(v___x_1036_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1045_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___lam__0___closed__1));
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 1);
lean_ctor_set(v___x_1043_, 1, v___x_1045_);
v___x_1047_ = v___x_1043_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_pos_1037_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
else
{
return v___x_1036_;
}
}
}
static lean_object* _init_l_Std_Http_Request_Builder_uri_x21___closed__5(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1065_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__4));
v___x_1066_ = lean_unsigned_to_nat(12u);
v___x_1067_ = lean_unsigned_to_nat(45u);
v___x_1068_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__3));
v___x_1069_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__2));
v___x_1070_ = l_mkPanicMessageWithDecl(v___x_1069_, v___x_1068_, v___x_1067_, v___x_1066_, v___x_1065_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21(lean_object* v_builder_1071_, lean_object* v_uri_1072_){
_start:
{
lean_object* v___y_1074_; lean_object* v___f_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___f_1095_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__1));
v___x_1096_ = lean_string_to_utf8(v_uri_1072_);
v___x_1097_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1095_, v___x_1096_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec_ref_known(v___x_1097_, 1);
v___x_1098_ = lean_obj_once(&l_Std_Http_Request_Builder_uri_x21___closed__5, &l_Std_Http_Request_Builder_uri_x21___closed__5_once, _init_l_Std_Http_Request_Builder_uri_x21___closed__5);
v___x_1099_ = l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(v___x_1098_);
v___y_1074_ = v___x_1099_;
goto v___jp_1073_;
}
else
{
lean_object* v_a_1100_; 
v_a_1100_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1097_, 1);
v___y_1074_ = v_a_1100_;
goto v___jp_1073_;
}
v___jp_1073_:
{
lean_object* v_line_1075_; lean_object* v_extensions_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1094_; 
v_line_1075_ = lean_ctor_get(v_builder_1071_, 0);
v_extensions_1076_ = lean_ctor_get(v_builder_1071_, 1);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_builder_1071_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1078_ = v_builder_1071_;
v_isShared_1079_ = v_isSharedCheck_1094_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_extensions_1076_);
lean_inc(v_line_1075_);
lean_dec(v_builder_1071_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1094_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
uint8_t v_method_1080_; uint8_t v_version_1081_; lean_object* v_headers_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1092_; 
v_method_1080_ = lean_ctor_get_uint8(v_line_1075_, sizeof(void*)*2);
v_version_1081_ = lean_ctor_get_uint8(v_line_1075_, sizeof(void*)*2 + 1);
v_headers_1082_ = lean_ctor_get(v_line_1075_, 1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_line_1075_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; 
v_unused_1093_ = lean_ctor_get(v_line_1075_, 0);
lean_dec(v_unused_1093_);
v___x_1084_ = v_line_1075_;
v_isShared_1085_ = v_isSharedCheck_1092_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_headers_1082_);
lean_dec(v_line_1075_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1092_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___y_1074_);
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___y_1074_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_headers_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1091_, sizeof(void*)*2, v_method_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1091_, sizeof(void*)*2 + 1, v_version_1081_);
v___x_1087_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1089_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1087_);
v___x_1089_ = v___x_1078_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_extensions_1076_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headers(lean_object* v_builder_1101_, lean_object* v_headers_1102_){
_start:
{
lean_object* v_line_1103_; lean_object* v_extensions_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1122_; 
v_line_1103_ = lean_ctor_get(v_builder_1101_, 0);
v_extensions_1104_ = lean_ctor_get(v_builder_1101_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_builder_1101_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1106_ = v_builder_1101_;
v_isShared_1107_ = v_isSharedCheck_1122_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_extensions_1104_);
lean_inc(v_line_1103_);
lean_dec(v_builder_1101_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1122_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
uint8_t v_method_1108_; uint8_t v_version_1109_; lean_object* v_uri_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1120_; 
v_method_1108_ = lean_ctor_get_uint8(v_line_1103_, sizeof(void*)*2);
v_version_1109_ = lean_ctor_get_uint8(v_line_1103_, sizeof(void*)*2 + 1);
v_uri_1110_ = lean_ctor_get(v_line_1103_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_line_1103_);
if (v_isSharedCheck_1120_ == 0)
{
lean_object* v_unused_1121_; 
v_unused_1121_ = lean_ctor_get(v_line_1103_, 1);
lean_dec(v_unused_1121_);
v___x_1112_ = v_line_1103_;
v_isShared_1113_ = v_isSharedCheck_1120_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_uri_1110_);
lean_dec(v_line_1103_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1120_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 1, v_headers_1102_);
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_uri_1110_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_headers_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, sizeof(void*)*2, v_method_1108_);
lean_ctor_set_uint8(v_reuseFailAlloc_1119_, sizeof(void*)*2 + 1, v_version_1109_);
v___x_1115_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1117_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1115_);
v___x_1117_ = v___x_1106_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_extensions_1104_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header(lean_object* v_builder_1123_, lean_object* v_key_1124_, lean_object* v_value_1125_){
_start:
{
lean_object* v_line_1126_; lean_object* v_extensions_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1147_; 
v_line_1126_ = lean_ctor_get(v_builder_1123_, 0);
v_extensions_1127_ = lean_ctor_get(v_builder_1123_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_builder_1123_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1129_ = v_builder_1123_;
v_isShared_1130_ = v_isSharedCheck_1147_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_extensions_1127_);
lean_inc(v_line_1126_);
lean_dec(v_builder_1123_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1147_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint8_t v_method_1131_; uint8_t v_version_1132_; lean_object* v_uri_1133_; lean_object* v_headers_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1146_; 
v_method_1131_ = lean_ctor_get_uint8(v_line_1126_, sizeof(void*)*2);
v_version_1132_ = lean_ctor_get_uint8(v_line_1126_, sizeof(void*)*2 + 1);
v_uri_1133_ = lean_ctor_get(v_line_1126_, 0);
v_headers_1134_ = lean_ctor_get(v_line_1126_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_line_1126_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1136_ = v_line_1126_;
v_isShared_1137_ = v_isSharedCheck_1146_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_headers_1134_);
lean_inc(v_uri_1133_);
lean_dec(v_line_1126_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1146_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v_key_1124_);
lean_ctor_set(v___x_1138_, 1, v_value_1125_);
v___x_1139_ = lean_array_push(v_headers_1134_, v___x_1138_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1139_);
v___x_1141_ = v___x_1136_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_uri_1133_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v___x_1139_);
lean_ctor_set_uint8(v_reuseFailAlloc_1145_, sizeof(void*)*2, v_method_1131_);
lean_ctor_set_uint8(v_reuseFailAlloc_1145_, sizeof(void*)*2 + 1, v_version_1132_);
v___x_1141_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1143_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1141_);
v___x_1143_ = v___x_1129_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_extensions_1127_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x21(lean_object* v_builder_1148_, lean_object* v_key_1149_, lean_object* v_value_1150_){
_start:
{
lean_object* v_line_1151_; lean_object* v_extensions_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1174_; 
v_line_1151_ = lean_ctor_get(v_builder_1148_, 0);
v_extensions_1152_ = lean_ctor_get(v_builder_1148_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_builder_1148_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1154_ = v_builder_1148_;
v_isShared_1155_ = v_isSharedCheck_1174_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_extensions_1152_);
lean_inc(v_line_1151_);
lean_dec(v_builder_1148_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1174_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
uint8_t v_method_1156_; uint8_t v_version_1157_; lean_object* v_uri_1158_; lean_object* v_headers_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1173_; 
v_method_1156_ = lean_ctor_get_uint8(v_line_1151_, sizeof(void*)*2);
v_version_1157_ = lean_ctor_get_uint8(v_line_1151_, sizeof(void*)*2 + 1);
v_uri_1158_ = lean_ctor_get(v_line_1151_, 0);
v_headers_1159_ = lean_ctor_get(v_line_1151_, 1);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_line_1151_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1161_ = v_line_1151_;
v_isShared_1162_ = v_isSharedCheck_1173_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_headers_1159_);
lean_inc(v_uri_1158_);
lean_dec(v_line_1151_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1173_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v_key_1163_; lean_object* v_value_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v_key_1163_ = l_Std_Http_Header_Name_ofString_x21(v_key_1149_);
v_value_1164_ = l_Std_Http_Header_Value_ofString_x21(v_value_1150_);
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v_key_1163_);
lean_ctor_set(v___x_1165_, 1, v_value_1164_);
v___x_1166_ = lean_array_push(v_headers_1159_, v___x_1165_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1166_);
v___x_1168_ = v___x_1161_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_uri_1158_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v___x_1166_);
lean_ctor_set_uint8(v_reuseFailAlloc_1172_, sizeof(void*)*2, v_method_1156_);
lean_ctor_set_uint8(v_reuseFailAlloc_1172_, sizeof(void*)*2 + 1, v_version_1157_);
v___x_1168_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1170_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1168_);
v___x_1170_ = v___x_1154_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_extensions_1152_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x3f(lean_object* v_builder_1175_, lean_object* v_key_1176_, lean_object* v_value_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Std_Http_Header_Name_ofString_x3f(v_key_1176_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v___x_1179_; 
lean_dec_ref(v_value_1177_);
lean_dec_ref(v_builder_1175_);
v___x_1179_ = lean_box(0);
return v___x_1179_;
}
else
{
lean_object* v_val_1180_; lean_object* v___x_1181_; 
v_val_1180_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_val_1180_);
lean_dec_ref_known(v___x_1178_, 1);
v___x_1181_ = l_Std_Http_Header_Value_ofString_x3f(v_value_1177_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v___x_1182_; 
lean_dec(v_val_1180_);
lean_dec_ref(v_builder_1175_);
v___x_1182_ = lean_box(0);
return v___x_1182_;
}
else
{
lean_object* v_line_1183_; lean_object* v_val_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1213_; 
v_line_1183_ = lean_ctor_get(v_builder_1175_, 0);
lean_inc_ref(v_line_1183_);
v_val_1184_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1186_ = v___x_1181_;
v_isShared_1187_ = v_isSharedCheck_1213_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_val_1184_);
lean_dec(v___x_1181_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1213_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_extensions_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1211_; 
v_extensions_1188_ = lean_ctor_get(v_builder_1175_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_builder_1175_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v_builder_1175_, 0);
lean_dec(v_unused_1212_);
v___x_1190_ = v_builder_1175_;
v_isShared_1191_ = v_isSharedCheck_1211_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_extensions_1188_);
lean_dec(v_builder_1175_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1211_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
uint8_t v_method_1192_; uint8_t v_version_1193_; lean_object* v_uri_1194_; lean_object* v_headers_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1210_; 
v_method_1192_ = lean_ctor_get_uint8(v_line_1183_, sizeof(void*)*2);
v_version_1193_ = lean_ctor_get_uint8(v_line_1183_, sizeof(void*)*2 + 1);
v_uri_1194_ = lean_ctor_get(v_line_1183_, 0);
v_headers_1195_ = lean_ctor_get(v_line_1183_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_line_1183_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1197_ = v_line_1183_;
v_isShared_1198_ = v_isSharedCheck_1210_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_headers_1195_);
lean_inc(v_uri_1194_);
lean_dec(v_line_1183_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1210_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v_val_1180_);
lean_ctor_set(v___x_1199_, 1, v_val_1184_);
v___x_1200_ = lean_array_push(v_headers_1195_, v___x_1199_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 1, v___x_1200_);
v___x_1202_ = v___x_1197_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_uri_1194_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1200_);
lean_ctor_set_uint8(v_reuseFailAlloc_1209_, sizeof(void*)*2, v_method_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1209_, sizeof(void*)*2 + 1, v_version_1193_);
v___x_1202_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1204_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1202_);
v___x_1204_ = v___x_1190_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_extensions_1188_);
v___x_1204_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1206_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1204_);
v___x_1206_ = v___x_1186_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
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
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headerOpt(lean_object* v_builder_1214_, lean_object* v_key_1215_, lean_object* v_value_1216_){
_start:
{
if (lean_obj_tag(v_value_1216_) == 0)
{
lean_dec_ref(v_key_1215_);
return v_builder_1214_;
}
else
{
lean_object* v_val_1217_; lean_object* v___x_1218_; 
v_val_1217_ = lean_ctor_get(v_value_1216_, 0);
lean_inc(v_val_1217_);
lean_dec_ref_known(v_value_1216_, 1);
v___x_1218_ = l_Std_Http_Request_Builder_header(v_builder_1214_, v_key_1215_, v_val_1217_);
return v___x_1218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension___redArg(lean_object* v_builder_1220_, lean_object* v_inst_1221_, lean_object* v_data_1222_){
_start:
{
lean_object* v_line_1223_; lean_object* v_extensions_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1235_; 
v_line_1223_ = lean_ctor_get(v_builder_1220_, 0);
v_extensions_1224_ = lean_ctor_get(v_builder_1220_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_builder_1220_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1226_ = v_builder_1220_;
v_isShared_1227_ = v_isSharedCheck_1235_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_extensions_1224_);
lean_inc(v_line_1223_);
lean_dec(v_builder_1220_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1235_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v_dyn_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1233_; 
v_dyn_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_1228_, 0, v_inst_1221_);
lean_ctor_set(v_dyn_1228_, 1, v_data_1222_);
v___x_1229_ = ((lean_object*)(l_Std_Http_Request_Builder_extension___redArg___closed__0));
v___x_1230_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_1228_);
v___x_1231_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1229_, v___x_1230_, v_dyn_1228_, v_extensions_1224_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v___x_1231_);
v___x_1233_ = v___x_1226_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_line_1223_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension(lean_object* v_00_u03b1_1236_, lean_object* v_builder_1237_, lean_object* v_inst_1238_, lean_object* v_data_1239_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Std_Http_Request_Builder_extension___redArg(v_builder_1237_, v_inst_1238_, v_data_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object* v_builder_1241_, lean_object* v_body_1242_){
_start:
{
lean_object* v_line_1243_; lean_object* v_extensions_1244_; lean_object* v___x_1245_; 
v_line_1243_ = lean_ctor_get(v_builder_1241_, 0);
v_extensions_1244_ = lean_ctor_get(v_builder_1241_, 1);
lean_inc(v_extensions_1244_);
lean_inc_ref(v_line_1243_);
v___x_1245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1245_, 0, v_line_1243_);
lean_ctor_set(v___x_1245_, 1, v_body_1242_);
lean_ctor_set(v___x_1245_, 2, v_extensions_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg___boxed(lean_object* v_builder_1246_, lean_object* v_body_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1246_, v_body_1247_);
lean_dec_ref(v_builder_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body(lean_object* v_t_1249_, lean_object* v_builder_1250_, lean_object* v_body_1251_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1250_, v_body_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___boxed(lean_object* v_t_1253_, lean_object* v_builder_1254_, lean_object* v_body_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Std_Http_Request_Builder_body(v_t_1253_, v_builder_1254_, v_body_1255_);
lean_dec_ref(v_builder_1254_);
return v_res_1256_;
}
}
static lean_object* _init_l_Std_Http_Request_get___closed__0(void){
_start:
{
uint8_t v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = 8;
v___x_1258_ = l_Std_Http_Request_new;
v___x_1259_ = l_Std_Http_Request_Builder_method(v___x_1258_, v___x_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_get(lean_object* v_uri_1260_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_obj_once(&l_Std_Http_Request_get___closed__0, &l_Std_Http_Request_get___closed__0_once, _init_l_Std_Http_Request_get___closed__0);
v___x_1262_ = l_Std_Http_Request_Builder_uri(v___x_1261_, v_uri_1260_);
return v___x_1262_;
}
}
static lean_object* _init_l_Std_Http_Request_post___closed__0(void){
_start:
{
uint8_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = 23;
v___x_1264_ = l_Std_Http_Request_new;
v___x_1265_ = l_Std_Http_Request_Builder_method(v___x_1264_, v___x_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_post(lean_object* v_uri_1266_){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_obj_once(&l_Std_Http_Request_post___closed__0, &l_Std_Http_Request_post___closed__0_once, _init_l_Std_Http_Request_post___closed__0);
v___x_1268_ = l_Std_Http_Request_Builder_uri(v___x_1267_, v_uri_1266_);
return v___x_1268_;
}
}
static lean_object* _init_l_Std_Http_Request_put___closed__0(void){
_start:
{
uint8_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = 27;
v___x_1270_ = l_Std_Http_Request_new;
v___x_1271_ = l_Std_Http_Request_Builder_method(v___x_1270_, v___x_1269_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_put(lean_object* v_uri_1272_){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = lean_obj_once(&l_Std_Http_Request_put___closed__0, &l_Std_Http_Request_put___closed__0_once, _init_l_Std_Http_Request_put___closed__0);
v___x_1274_ = l_Std_Http_Request_Builder_uri(v___x_1273_, v_uri_1272_);
return v___x_1274_;
}
}
static lean_object* _init_l_Std_Http_Request_delete___closed__0(void){
_start:
{
uint8_t v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = 7;
v___x_1276_ = l_Std_Http_Request_new;
v___x_1277_ = l_Std_Http_Request_Builder_method(v___x_1276_, v___x_1275_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_delete(lean_object* v_uri_1278_){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_obj_once(&l_Std_Http_Request_delete___closed__0, &l_Std_Http_Request_delete___closed__0_once, _init_l_Std_Http_Request_delete___closed__0);
v___x_1280_ = l_Std_Http_Request_Builder_uri(v___x_1279_, v_uri_1278_);
return v___x_1280_;
}
}
static lean_object* _init_l_Std_Http_Request_patch___closed__0(void){
_start:
{
uint8_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = 22;
v___x_1282_ = l_Std_Http_Request_new;
v___x_1283_ = l_Std_Http_Request_Builder_method(v___x_1282_, v___x_1281_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_patch(lean_object* v_uri_1284_){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_obj_once(&l_Std_Http_Request_patch___closed__0, &l_Std_Http_Request_patch___closed__0_once, _init_l_Std_Http_Request_patch___closed__0);
v___x_1286_ = l_Std_Http_Request_Builder_uri(v___x_1285_, v_uri_1284_);
return v___x_1286_;
}
}
static lean_object* _init_l_Std_Http_Request_head___closed__0(void){
_start:
{
uint8_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = 9;
v___x_1288_ = l_Std_Http_Request_new;
v___x_1289_ = l_Std_Http_Request_Builder_method(v___x_1288_, v___x_1287_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_head(lean_object* v_uri_1290_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_obj_once(&l_Std_Http_Request_head___closed__0, &l_Std_Http_Request_head___closed__0_once, _init_l_Std_Http_Request_head___closed__0);
v___x_1292_ = l_Std_Http_Request_Builder_uri(v___x_1291_, v_uri_1290_);
return v___x_1292_;
}
}
static lean_object* _init_l_Std_Http_Request_options___closed__0(void){
_start:
{
uint8_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = 20;
v___x_1294_ = l_Std_Http_Request_new;
v___x_1295_ = l_Std_Http_Request_Builder_method(v___x_1294_, v___x_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_options(lean_object* v_uri_1296_){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_obj_once(&l_Std_Http_Request_options___closed__0, &l_Std_Http_Request_options___closed__0_once, _init_l_Std_Http_Request_options___closed__0);
v___x_1298_ = l_Std_Http_Request_Builder_uri(v___x_1297_, v_uri_1296_);
return v___x_1298_;
}
}
static lean_object* _init_l_Std_Http_Request_connect___closed__0(void){
_start:
{
uint8_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = 5;
v___x_1300_ = l_Std_Http_Request_new;
v___x_1301_ = l_Std_Http_Request_Builder_method(v___x_1300_, v___x_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_connect(lean_object* v_uri_1302_){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_obj_once(&l_Std_Http_Request_connect___closed__0, &l_Std_Http_Request_connect___closed__0_once, _init_l_Std_Http_Request_connect___closed__0);
v___x_1304_ = l_Std_Http_Request_Builder_uri(v___x_1303_, v_uri_1302_);
return v___x_1304_;
}
}
static lean_object* _init_l_Std_Http_Request_trace___closed__0(void){
_start:
{
uint8_t v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = 32;
v___x_1306_ = l_Std_Http_Request_new;
v___x_1307_ = l_Std_Http_Request_Builder_method(v___x_1306_, v___x_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_trace(lean_object* v_uri_1308_){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_obj_once(&l_Std_Http_Request_trace___closed__0, &l_Std_Http_Request_trace___closed__0_once, _init_l_Std_Http_Request_trace___closed__0);
v___x_1310_ = l_Std_Http_Request_Builder_uri(v___x_1309_, v_uri_1308_);
return v___x_1310_;
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
