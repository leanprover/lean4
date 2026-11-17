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
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Http_Internal_appendFieldLine___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Headers_fold___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_Http_URI_Path_render(lean_object*, uint8_t, uint8_t);
lean_object* l_Std_Http_URI_Query_formatOption(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_uv_ntop_v4(lean_object*);
lean_object* lean_uv_ntop_v6(lean_object*);
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_Extensions_empty;
extern lean_object* l_Std_Http_Headers_empty;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
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
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__1___closed__0 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__1___closed__0_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__1___closed__1 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__1___closed__1_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__1___closed__2 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__1___closed__2_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__1___closed__3 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__1(lean_object*);
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__0_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__1 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__1_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__2 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__2_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__3 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__3_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__4 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__4_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__5 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__5_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__6 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__6_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__7 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__7_value;
static const lean_ctor_object l_Std_Http_Request_instToStringHead___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__1_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__2_value)}};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__8 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__8_value;
static const lean_ctor_object l_Std_Http_Request_instToStringHead___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__8_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__3_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__4_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__5_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__6_value)}};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__9 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__9_value;
static const lean_ctor_object l_Std_Http_Request_instToStringHead___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__9_value),((lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__7_value)}};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__10 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__10_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.0"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__11 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__11_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.1"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__12 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__12_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/2.0"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__13 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__13_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/3.0"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__14 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__14_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__15 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__15_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__16 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__16_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__17 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__17_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "//"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__18 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__18_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__19 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__19_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__20 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__20_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__21 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__21_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ACL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__22 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__22_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BASELINE-CONTROL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__23 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__23_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "BIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__24 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__24_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CHECKIN"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__25 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__25_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CHECKOUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__26 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__26_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CONNECT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__27 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__27_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COPY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__28 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__28_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DELETE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__29 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__29_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__30 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__30_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__31 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__31_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "LABEL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__32 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__32_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LINK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__33 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__33_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LOCK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__34 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__34_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MERGE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__35 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__35_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKACTIVITY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__36 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__36_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKCALENDAR"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__37 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__37_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MKCOL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__38 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__38_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MKREDIRECTREF"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__39 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__39_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MKWORKSPACE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__40 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__40_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MOVE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__41 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__41_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__42 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__42_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ORDERPATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__43 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__43_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__44 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__44_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__45 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__45_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRI"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__46 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__46_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PROPFIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__47 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__47_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PROPPATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__48 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__48_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__49 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__49_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "QUERY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__50 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__50_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REBIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__51 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__51_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REPORT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__52 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__52_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SEARCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__53 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__53_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TRACE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__54 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__54_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNBIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__55 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__55_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UNCHECKOUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__56 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__56_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLINK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__57 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__57_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLOCK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__58 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__58_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UPDATE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__59 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__59_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UPDATEREDIRECTREF"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__60 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__60_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "VERSION-CONTROL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__61 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__61_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__0 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__2, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value)} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__1 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Request_instToStringHead = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__1_value;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1;
static const lean_closure_object l_Std_Http_Request_instEncodeV11Head___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_appendFieldLine___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___closed__2 = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__2_value;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___closed__5;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___closed__6;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___closed__7;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___closed__8;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___closed__9;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___closed__10;
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Request_instEncodeV11Head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instEncodeV11Head___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_ctor_object l_Std_Http_Request_Builder_uri_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*9 + 0, .m_other = 9, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(64) << 1) | 1)),((lean_object*)(((size_t)(253) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__0(lean_object* v___x_122_, lean_object* v___x_123_, lean_object* v___x_124_, lean_object* v_fst_125_, lean_object* v___x_126_, uint32_t v___x_127_, lean_object* v___x_128_, lean_object* v_it_129_, lean_object* v_acc_130_, lean_object* v_hP_131_, lean_object* v_recur_132_){
_start:
{
lean_object* v_it_134_; lean_object* v_out_135_; lean_object* v_it_151_; lean_object* v_startInclusive_152_; lean_object* v_endExclusive_153_; 
if (lean_obj_tag(v_it_129_) == 0)
{
lean_object* v_currPos_165_; lean_object* v_searcher_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_188_; 
v_currPos_165_ = lean_ctor_get(v_it_129_, 0);
v_searcher_166_ = lean_ctor_get(v_it_129_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_it_129_);
if (v_isSharedCheck_188_ == 0)
{
v___x_168_ = v_it_129_;
v_isShared_169_ = v_isSharedCheck_188_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_searcher_166_);
lean_inc(v_currPos_165_);
lean_dec(v_it_129_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_188_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
uint8_t v_decide_170_; 
v_decide_170_ = lean_nat_dec_eq(v_searcher_166_, v___x_126_);
if (v_decide_170_ == 0)
{
uint32_t v___x_171_; uint8_t v___x_172_; 
lean_dec(v___x_126_);
v___x_171_ = lean_string_utf8_get_fast(v_fst_125_, v_searcher_166_);
v___x_172_ = lean_uint32_dec_eq(v___x_171_, v___x_127_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_173_ = lean_string_utf8_next_fast(v_fst_125_, v_searcher_166_);
lean_dec(v_searcher_166_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v___x_173_);
v___x_175_ = v___x_168_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_currPos_165_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v___x_173_);
v___x_175_ = v_reuseFailAlloc_177_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_176_; 
v___x_176_ = lean_apply_4(v_recur_132_, v___x_175_, v_acc_130_, lean_box(0), lean_box(0));
return v___x_176_;
}
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_slice_181_; lean_object* v_nextIt_183_; 
v___x_178_ = lean_string_utf8_next_fast(v_fst_125_, v_searcher_166_);
v___x_179_ = lean_nat_sub(v___x_178_, v_searcher_166_);
v___x_180_ = lean_nat_add(v_searcher_166_, v___x_179_);
lean_dec(v___x_179_);
v_slice_181_ = l_String_Slice_subslice_x21(v___x_128_, v_currPos_165_, v_searcher_166_);
lean_inc(v___x_180_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v___x_180_);
lean_ctor_set(v___x_168_, 0, v___x_180_);
v_nextIt_183_ = v___x_168_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v___x_180_);
v_nextIt_183_ = v_reuseFailAlloc_186_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v_startInclusive_184_; lean_object* v_endExclusive_185_; 
v_startInclusive_184_ = lean_ctor_get(v_slice_181_, 0);
lean_inc(v_startInclusive_184_);
v_endExclusive_185_ = lean_ctor_get(v_slice_181_, 1);
lean_inc(v_endExclusive_185_);
lean_dec_ref(v_slice_181_);
v_it_151_ = v_nextIt_183_;
v_startInclusive_152_ = v_startInclusive_184_;
v_endExclusive_153_ = v_endExclusive_185_;
goto v___jp_150_;
}
}
}
else
{
lean_object* v___x_187_; 
lean_del_object(v___x_168_);
lean_dec(v_searcher_166_);
v___x_187_ = lean_box(1);
v_it_151_ = v___x_187_;
v_startInclusive_152_ = v_currPos_165_;
v_endExclusive_153_ = v___x_126_;
goto v___jp_150_;
}
}
}
else
{
lean_dec_ref(v_recur_132_);
lean_dec(v___x_126_);
return v_acc_130_;
}
v___jp_133_:
{
if (lean_obj_tag(v_acc_130_) == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_136_, 0, v_out_135_);
v___x_137_ = lean_apply_4(v_recur_132_, v_it_134_, v___x_136_, lean_box(0), lean_box(0));
return v___x_137_;
}
else
{
lean_object* v_val_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_149_; 
v_val_138_ = lean_ctor_get(v_acc_130_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v_acc_130_);
if (v_isSharedCheck_149_ == 0)
{
v___x_140_ = v_acc_130_;
v_isShared_141_ = v_isSharedCheck_149_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_val_138_);
lean_dec(v_acc_130_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_149_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_142_ = lean_string_utf8_extract_fast(v___x_122_, v___x_123_, v___x_124_);
v___x_143_ = lean_string_append(v_val_138_, v___x_142_);
lean_dec_ref(v___x_142_);
v___x_144_ = lean_string_append(v___x_143_, v_out_135_);
lean_dec_ref(v_out_135_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_144_);
v___x_146_ = v___x_140_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_148_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; 
v___x_147_ = lean_apply_4(v_recur_132_, v_it_134_, v___x_146_, lean_box(0), lean_box(0));
return v___x_147_;
}
}
}
}
v___jp_150_:
{
lean_object* v___x_154_; uint32_t v___x_155_; uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_154_ = lean_string_utf8_extract_fast(v_fst_125_, v_startInclusive_152_, v_endExclusive_153_);
lean_dec(v_endExclusive_153_);
lean_dec(v_startInclusive_152_);
v___x_155_ = lean_string_utf8_get(v___x_154_, v___x_123_);
v___x_156_ = 97;
v___x_157_ = lean_uint32_dec_le(v___x_156_, v___x_155_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
v___x_158_ = lean_string_utf8_set(v___x_154_, v___x_123_, v___x_155_);
v_it_134_ = v_it_151_;
v_out_135_ = v___x_158_;
goto v___jp_133_;
}
else
{
uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 122;
v___x_160_ = lean_uint32_dec_le(v___x_155_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
v___x_161_ = lean_string_utf8_set(v___x_154_, v___x_123_, v___x_155_);
v_it_134_ = v_it_151_;
v_out_135_ = v___x_161_;
goto v___jp_133_;
}
else
{
uint32_t v___x_162_; uint32_t v___x_163_; lean_object* v___x_164_; 
v___x_162_ = 4294967264;
v___x_163_ = lean_uint32_add(v___x_155_, v___x_162_);
v___x_164_ = lean_string_utf8_set(v___x_154_, v___x_123_, v___x_163_);
v_it_134_ = v_it_151_;
v_out_135_ = v___x_164_;
goto v___jp_133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__0___boxed(lean_object* v___x_189_, lean_object* v___x_190_, lean_object* v___x_191_, lean_object* v_fst_192_, lean_object* v___x_193_, lean_object* v___x_194_, lean_object* v___x_195_, lean_object* v_it_196_, lean_object* v_acc_197_, lean_object* v_hP_198_, lean_object* v_recur_199_){
_start:
{
uint32_t v___x_1395__boxed_200_; lean_object* v_res_201_; 
v___x_1395__boxed_200_ = lean_unbox_uint32(v___x_194_);
lean_dec(v___x_194_);
v_res_201_ = l_Std_Http_Request_instToStringHead___lam__0(v___x_189_, v___x_190_, v___x_191_, v_fst_192_, v___x_193_, v___x_1395__boxed_200_, v___x_195_, v_it_196_, v_acc_197_, v_hP_198_, v_recur_199_);
lean_dec_ref(v___x_195_);
lean_dec_ref(v_fst_192_);
lean_dec(v___x_191_);
lean_dec(v___x_190_);
lean_dec_ref(v___x_189_);
return v_res_201_;
}
}
static lean_object* _init_l_Std_Http_Request_instToStringHead___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_206_; lean_object* v___x_207_; 
v___x_206_ = 45;
v___x_207_ = lean_box_uint32(v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__1(lean_object* v_x_208_){
_start:
{
lean_object* v_fst_209_; lean_object* v_snd_210_; lean_object* v___y_212_; lean_object* v___f_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v_it_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___f_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_fst_209_ = lean_ctor_get(v_x_208_, 0);
lean_inc_n(v_fst_209_, 2);
v_snd_210_ = lean_ctor_get(v_x_208_, 1);
lean_inc(v_snd_210_);
lean_dec_ref(v_x_208_);
v___f_216_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__1));
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_string_utf8_byte_size(v_fst_209_);
v___x_219_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_219_, 0, v_fst_209_);
lean_ctor_set(v___x_219_, 1, v___x_217_);
lean_ctor_set(v___x_219_, 2, v___x_218_);
lean_inc_ref(v___x_219_);
v_it_220_ = l_String_Slice_splitToSubslice___redArg(v___x_219_, v___f_216_);
v___x_221_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__2));
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = l_Std_Http_Request_instToStringHead___lam__1___boxed__const__1;
v___f_224_ = lean_alloc_closure((void*)(l_Std_Http_Request_instToStringHead___lam__0___boxed), 11, 7);
lean_closure_set(v___f_224_, 0, v___x_221_);
lean_closure_set(v___f_224_, 1, v___x_217_);
lean_closure_set(v___f_224_, 2, v___x_222_);
lean_closure_set(v___f_224_, 3, v_fst_209_);
lean_closure_set(v___f_224_, 4, v___x_218_);
lean_closure_set(v___f_224_, 5, v___x_223_);
lean_closure_set(v___f_224_, 6, v___x_219_);
v___x_225_ = lean_box(0);
v___x_226_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_224_, v_it_220_, v___x_225_, lean_box(0));
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v___x_227_; 
v___x_227_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__3));
v___y_212_ = v___x_227_;
goto v___jp_211_;
}
else
{
lean_object* v_val_228_; 
v_val_228_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_val_228_);
lean_dec_ref_known(v___x_226_, 1);
v___y_212_ = v_val_228_;
goto v___jp_211_;
}
v___jp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__0));
v___x_214_ = lean_string_append(v___y_212_, v___x_213_);
v___x_215_ = lean_string_append(v___x_214_, v_snd_210_);
lean_dec(v_snd_210_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2(lean_object* v___f_300_, lean_object* v_req_301_){
_start:
{
uint8_t v_method_302_; uint8_t v_version_303_; lean_object* v_uri_304_; lean_object* v_headers_305_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; uint8_t v___y_344_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v_port_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_408_; 
v_method_302_ = lean_ctor_get_uint8(v_req_301_, sizeof(void*)*2);
v_version_303_ = lean_ctor_get_uint8(v_req_301_, sizeof(void*)*2 + 1);
v_uri_304_ = lean_ctor_get(v_req_301_, 0);
lean_inc(v_uri_304_);
v_headers_305_ = lean_ctor_get(v_req_301_, 1);
lean_inc_ref(v_headers_305_);
lean_dec_ref(v_req_301_);
switch(v_method_302_)
{
case 0:
{
lean_object* v___x_475_; 
v___x_475_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__22));
v___y_408_ = v___x_475_;
goto v___jp_407_;
}
case 1:
{
lean_object* v___x_476_; 
v___x_476_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__23));
v___y_408_ = v___x_476_;
goto v___jp_407_;
}
case 2:
{
lean_object* v___x_477_; 
v___x_477_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__24));
v___y_408_ = v___x_477_;
goto v___jp_407_;
}
case 3:
{
lean_object* v___x_478_; 
v___x_478_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__25));
v___y_408_ = v___x_478_;
goto v___jp_407_;
}
case 4:
{
lean_object* v___x_479_; 
v___x_479_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__26));
v___y_408_ = v___x_479_;
goto v___jp_407_;
}
case 5:
{
lean_object* v___x_480_; 
v___x_480_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__27));
v___y_408_ = v___x_480_;
goto v___jp_407_;
}
case 6:
{
lean_object* v___x_481_; 
v___x_481_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__28));
v___y_408_ = v___x_481_;
goto v___jp_407_;
}
case 7:
{
lean_object* v___x_482_; 
v___x_482_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__29));
v___y_408_ = v___x_482_;
goto v___jp_407_;
}
case 8:
{
lean_object* v___x_483_; 
v___x_483_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__30));
v___y_408_ = v___x_483_;
goto v___jp_407_;
}
case 9:
{
lean_object* v___x_484_; 
v___x_484_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__31));
v___y_408_ = v___x_484_;
goto v___jp_407_;
}
case 10:
{
lean_object* v___x_485_; 
v___x_485_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__32));
v___y_408_ = v___x_485_;
goto v___jp_407_;
}
case 11:
{
lean_object* v___x_486_; 
v___x_486_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__33));
v___y_408_ = v___x_486_;
goto v___jp_407_;
}
case 12:
{
lean_object* v___x_487_; 
v___x_487_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__34));
v___y_408_ = v___x_487_;
goto v___jp_407_;
}
case 13:
{
lean_object* v___x_488_; 
v___x_488_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__35));
v___y_408_ = v___x_488_;
goto v___jp_407_;
}
case 14:
{
lean_object* v___x_489_; 
v___x_489_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__36));
v___y_408_ = v___x_489_;
goto v___jp_407_;
}
case 15:
{
lean_object* v___x_490_; 
v___x_490_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__37));
v___y_408_ = v___x_490_;
goto v___jp_407_;
}
case 16:
{
lean_object* v___x_491_; 
v___x_491_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__38));
v___y_408_ = v___x_491_;
goto v___jp_407_;
}
case 17:
{
lean_object* v___x_492_; 
v___x_492_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__39));
v___y_408_ = v___x_492_;
goto v___jp_407_;
}
case 18:
{
lean_object* v___x_493_; 
v___x_493_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__40));
v___y_408_ = v___x_493_;
goto v___jp_407_;
}
case 19:
{
lean_object* v___x_494_; 
v___x_494_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__41));
v___y_408_ = v___x_494_;
goto v___jp_407_;
}
case 20:
{
lean_object* v___x_495_; 
v___x_495_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__42));
v___y_408_ = v___x_495_;
goto v___jp_407_;
}
case 21:
{
lean_object* v___x_496_; 
v___x_496_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__43));
v___y_408_ = v___x_496_;
goto v___jp_407_;
}
case 22:
{
lean_object* v___x_497_; 
v___x_497_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__44));
v___y_408_ = v___x_497_;
goto v___jp_407_;
}
case 23:
{
lean_object* v___x_498_; 
v___x_498_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__45));
v___y_408_ = v___x_498_;
goto v___jp_407_;
}
case 24:
{
lean_object* v___x_499_; 
v___x_499_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__46));
v___y_408_ = v___x_499_;
goto v___jp_407_;
}
case 25:
{
lean_object* v___x_500_; 
v___x_500_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__47));
v___y_408_ = v___x_500_;
goto v___jp_407_;
}
case 26:
{
lean_object* v___x_501_; 
v___x_501_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__48));
v___y_408_ = v___x_501_;
goto v___jp_407_;
}
case 27:
{
lean_object* v___x_502_; 
v___x_502_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__49));
v___y_408_ = v___x_502_;
goto v___jp_407_;
}
case 28:
{
lean_object* v___x_503_; 
v___x_503_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__50));
v___y_408_ = v___x_503_;
goto v___jp_407_;
}
case 29:
{
lean_object* v___x_504_; 
v___x_504_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__51));
v___y_408_ = v___x_504_;
goto v___jp_407_;
}
case 30:
{
lean_object* v___x_505_; 
v___x_505_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__52));
v___y_408_ = v___x_505_;
goto v___jp_407_;
}
case 31:
{
lean_object* v___x_506_; 
v___x_506_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__53));
v___y_408_ = v___x_506_;
goto v___jp_407_;
}
case 32:
{
lean_object* v___x_507_; 
v___x_507_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__54));
v___y_408_ = v___x_507_;
goto v___jp_407_;
}
case 33:
{
lean_object* v___x_508_; 
v___x_508_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__55));
v___y_408_ = v___x_508_;
goto v___jp_407_;
}
case 34:
{
lean_object* v___x_509_; 
v___x_509_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__56));
v___y_408_ = v___x_509_;
goto v___jp_407_;
}
case 35:
{
lean_object* v___x_510_; 
v___x_510_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__57));
v___y_408_ = v___x_510_;
goto v___jp_407_;
}
case 36:
{
lean_object* v___x_511_; 
v___x_511_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__58));
v___y_408_ = v___x_511_;
goto v___jp_407_;
}
case 37:
{
lean_object* v___x_512_; 
v___x_512_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__59));
v___y_408_ = v___x_512_;
goto v___jp_407_;
}
case 38:
{
lean_object* v___x_513_; 
v___x_513_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__60));
v___y_408_ = v___x_513_;
goto v___jp_407_;
}
default: 
{
lean_object* v___x_514_; 
v___x_514_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__61));
v___y_408_ = v___x_514_;
goto v___jp_407_;
}
}
v___jp_306_:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; size_t v_sz_313_; size_t v___x_314_; lean_object* v_pairs_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_309_ = lean_string_append(v___y_307_, v___y_308_);
v___x_310_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__0));
v___x_311_ = lean_string_append(v___x_309_, v___x_310_);
v___x_312_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__10));
v_sz_313_ = lean_array_size(v_headers_305_);
v___x_314_ = ((size_t)0ULL);
v_pairs_315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_312_, v___f_300_, v_sz_313_, v___x_314_, v_headers_305_);
v___x_316_ = lean_array_to_list(v_pairs_315_);
v___x_317_ = l_String_intercalate(v___x_310_, v___x_316_);
v___x_318_ = lean_string_append(v___x_311_, v___x_317_);
lean_dec_ref(v___x_317_);
v___x_319_ = lean_string_append(v___x_318_, v___x_310_);
return v___x_319_;
}
v___jp_320_:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_string_append(v___y_321_, v___y_323_);
lean_dec_ref(v___y_323_);
v___x_325_ = lean_string_append(v___x_324_, v___y_322_);
switch(v_version_303_)
{
case 0:
{
lean_object* v___x_326_; 
v___x_326_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__11));
v___y_307_ = v___x_325_;
v___y_308_ = v___x_326_;
goto v___jp_306_;
}
case 1:
{
lean_object* v___x_327_; 
v___x_327_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__12));
v___y_307_ = v___x_325_;
v___y_308_ = v___x_327_;
goto v___jp_306_;
}
case 2:
{
lean_object* v___x_328_; 
v___x_328_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__13));
v___y_307_ = v___x_325_;
v___y_308_ = v___x_328_;
goto v___jp_306_;
}
default: 
{
lean_object* v___x_329_; 
v___x_329_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__14));
v___y_307_ = v___x_325_;
v___y_308_ = v___x_329_;
goto v___jp_306_;
}
}
}
v___jp_330_:
{
lean_object* v_queryStr_335_; lean_object* v___x_336_; 
v_queryStr_335_ = l_Std_Http_URI_Query_formatOption(v___y_332_);
v___x_336_ = lean_string_append(v___y_334_, v_queryStr_335_);
lean_dec_ref(v_queryStr_335_);
v___y_321_ = v___y_331_;
v___y_322_ = v___y_333_;
v___y_323_ = v___x_336_;
goto v___jp_320_;
}
v___jp_337_:
{
uint8_t v___x_345_; lean_object* v_pathPart_346_; lean_object* v_queryPart_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_345_ = 1;
v_pathPart_346_ = l_Std_Http_URI_Path_render(v___y_338_, v___y_344_, v___x_345_);
v_queryPart_347_ = l_Std_Http_URI_Query_formatOption(v___y_342_);
v___x_348_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___x_349_ = lean_string_append(v___y_339_, v___x_348_);
v___x_350_ = lean_string_append(v___x_349_, v___y_341_);
lean_dec_ref(v___y_341_);
v___x_351_ = lean_string_append(v___x_350_, v_pathPart_346_);
lean_dec_ref(v_pathPart_346_);
v___x_352_ = lean_string_append(v___x_351_, v_queryPart_347_);
lean_dec_ref(v_queryPart_347_);
v___y_321_ = v___y_340_;
v___y_322_ = v___y_343_;
v___y_323_ = v___x_352_;
goto v___jp_320_;
}
v___jp_353_:
{
uint8_t v___x_360_; 
v___x_360_ = 0;
lean_inc_ref(v___y_359_);
v___y_338_ = v___y_354_;
v___y_339_ = v___y_355_;
v___y_340_ = v___y_356_;
v___y_341_ = v___y_359_;
v___y_342_ = v___y_357_;
v___y_343_ = v___y_358_;
v___y_344_ = v___x_360_;
goto v___jp_337_;
}
v___jp_361_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
lean_dec(v___y_363_);
v___x_372_ = lean_string_append(v___y_365_, v___y_369_);
lean_dec_ref(v___y_369_);
v___x_373_ = lean_string_append(v___x_372_, v___y_371_);
lean_dec_ref(v___y_371_);
lean_inc_ref(v___y_366_);
v___x_374_ = lean_string_append(v___y_366_, v___x_373_);
lean_dec_ref(v___x_373_);
v___x_375_ = 1;
v___y_338_ = v___y_362_;
v___y_339_ = v___y_364_;
v___y_340_ = v___y_367_;
v___y_341_ = v___x_374_;
v___y_342_ = v___y_368_;
v___y_343_ = v___y_370_;
v___y_344_ = v___x_375_;
goto v___jp_337_;
}
v___jp_376_:
{
switch(lean_obj_tag(v_port_379_))
{
case 0:
{
lean_object* v___x_387_; 
v___x_387_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__3));
v___y_362_ = v___y_378_;
v___y_363_ = v___y_377_;
v___y_364_ = v___y_380_;
v___y_365_ = v___y_381_;
v___y_366_ = v___y_382_;
v___y_367_ = v___y_383_;
v___y_368_ = v___y_384_;
v___y_369_ = v___y_386_;
v___y_370_ = v___y_385_;
v___y_371_ = v___x_387_;
goto v___jp_361_;
}
case 1:
{
lean_object* v___x_388_; 
v___x_388_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___y_362_ = v___y_378_;
v___y_363_ = v___y_377_;
v___y_364_ = v___y_380_;
v___y_365_ = v___y_381_;
v___y_366_ = v___y_382_;
v___y_367_ = v___y_383_;
v___y_368_ = v___y_384_;
v___y_369_ = v___y_386_;
v___y_370_ = v___y_385_;
v___y_371_ = v___x_388_;
goto v___jp_361_;
}
default: 
{
uint16_t v_port_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_port_389_ = lean_ctor_get_uint16(v_port_379_, 0);
lean_dec_ref_known(v_port_379_, 0);
v___x_390_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___x_391_ = lean_uint16_to_nat(v_port_389_);
v___x_392_ = l_Nat_reprFast(v___x_391_);
v___x_393_ = lean_string_append(v___x_390_, v___x_392_);
lean_dec_ref(v___x_392_);
v___y_362_ = v___y_378_;
v___y_363_ = v___y_377_;
v___y_364_ = v___y_380_;
v___y_365_ = v___y_381_;
v___y_366_ = v___y_382_;
v___y_367_ = v___y_383_;
v___y_368_ = v___y_384_;
v___y_369_ = v___y_386_;
v___y_370_ = v___y_385_;
v___y_371_ = v___x_393_;
goto v___jp_361_;
}
}
}
v___jp_394_:
{
switch(lean_obj_tag(v___y_395_))
{
case 0:
{
v___y_321_ = v___y_396_;
v___y_322_ = v___y_397_;
v___y_323_ = v___y_398_;
goto v___jp_320_;
}
case 1:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___x_400_ = lean_string_append(v___y_398_, v___x_399_);
v___y_321_ = v___y_396_;
v___y_322_ = v___y_397_;
v___y_323_ = v___x_400_;
goto v___jp_320_;
}
default: 
{
uint16_t v_port_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_port_401_ = lean_ctor_get_uint16(v___y_395_, 0);
lean_dec_ref_known(v___y_395_, 0);
v___x_402_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___x_403_ = lean_uint16_to_nat(v_port_401_);
v___x_404_ = l_Nat_reprFast(v___x_403_);
v___x_405_ = lean_string_append(v___x_402_, v___x_404_);
lean_dec_ref(v___x_404_);
v___x_406_ = lean_string_append(v___y_398_, v___x_405_);
lean_dec_ref(v___x_405_);
v___y_321_ = v___y_396_;
v___y_322_ = v___y_397_;
v___y_323_ = v___x_406_;
goto v___jp_320_;
}
}
}
v___jp_407_:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__16));
lean_inc_ref(v___y_408_);
v___x_410_ = lean_string_append(v___y_408_, v___x_409_);
switch(lean_obj_tag(v_uri_304_))
{
case 0:
{
lean_object* v_path_411_; lean_object* v_query_412_; uint8_t v___x_413_; lean_object* v_pathStr_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_path_411_ = lean_ctor_get(v_uri_304_, 0);
lean_inc_ref(v_path_411_);
v_query_412_ = lean_ctor_get(v_uri_304_, 1);
lean_inc(v_query_412_);
lean_dec_ref_known(v_uri_304_, 2);
v___x_413_ = 1;
v_pathStr_414_ = l_Std_Http_URI_Path_render(v_path_411_, v___x_413_, v___x_413_);
v___x_415_ = lean_string_utf8_byte_size(v_pathStr_414_);
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = lean_nat_dec_eq(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
v___y_331_ = v___x_410_;
v___y_332_ = v_query_412_;
v___y_333_ = v___x_409_;
v___y_334_ = v_pathStr_414_;
goto v___jp_330_;
}
else
{
lean_object* v___x_418_; 
lean_dec_ref(v_pathStr_414_);
v___x_418_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__17));
v___y_331_ = v___x_410_;
v___y_332_ = v_query_412_;
v___y_333_ = v___x_409_;
v___y_334_ = v___x_418_;
goto v___jp_330_;
}
}
case 1:
{
lean_object* v_uri_419_; lean_object* v_authority_420_; 
v_uri_419_ = lean_ctor_get(v_uri_304_, 0);
lean_inc_ref(v_uri_419_);
lean_dec_ref_known(v_uri_304_, 1);
v_authority_420_ = lean_ctor_get(v_uri_419_, 1);
lean_inc(v_authority_420_);
if (lean_obj_tag(v_authority_420_) == 0)
{
lean_object* v_scheme_421_; lean_object* v_path_422_; lean_object* v_query_423_; lean_object* v___x_424_; 
v_scheme_421_ = lean_ctor_get(v_uri_419_, 0);
lean_inc_ref(v_scheme_421_);
v_path_422_ = lean_ctor_get(v_uri_419_, 2);
lean_inc_ref(v_path_422_);
v_query_423_ = lean_ctor_get(v_uri_419_, 3);
lean_inc(v_query_423_);
lean_dec_ref(v_uri_419_);
v___x_424_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__3));
v___y_354_ = v_path_422_;
v___y_355_ = v_scheme_421_;
v___y_356_ = v___x_410_;
v___y_357_ = v_query_423_;
v___y_358_ = v___x_409_;
v___y_359_ = v___x_424_;
goto v___jp_353_;
}
else
{
lean_object* v_val_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_457_; 
v_val_425_ = lean_ctor_get(v_authority_420_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_authority_420_);
if (v_isSharedCheck_457_ == 0)
{
v___x_427_ = v_authority_420_;
v_isShared_428_ = v_isSharedCheck_457_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_val_425_);
lean_dec(v_authority_420_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_457_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v_scheme_429_; lean_object* v_path_430_; lean_object* v_query_431_; lean_object* v_host_432_; lean_object* v_port_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_455_; 
v_scheme_429_ = lean_ctor_get(v_uri_419_, 0);
lean_inc_ref(v_scheme_429_);
v_path_430_ = lean_ctor_get(v_uri_419_, 2);
lean_inc_ref(v_path_430_);
v_query_431_ = lean_ctor_get(v_uri_419_, 3);
lean_inc(v_query_431_);
lean_dec_ref(v_uri_419_);
v_host_432_ = lean_ctor_get(v_val_425_, 1);
v_port_433_ = lean_ctor_get(v_val_425_, 2);
v_isSharedCheck_455_ = !lean_is_exclusive(v_val_425_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; 
v_unused_456_ = lean_ctor_get(v_val_425_, 0);
lean_dec(v_unused_456_);
v___x_435_ = v_val_425_;
v_isShared_436_ = v_isSharedCheck_455_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_port_433_);
lean_inc(v_host_432_);
lean_dec(v_val_425_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_455_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_437_ = lean_box(0);
lean_inc(v_port_433_);
lean_inc(v_host_432_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_437_);
v___x_439_ = v___x_435_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_host_432_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_port_433_);
v___x_439_ = v_reuseFailAlloc_454_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_441_; 
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_439_);
v___x_441_ = v___x_427_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_453_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__18));
v___x_443_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__3));
switch(lean_obj_tag(v_host_432_))
{
case 0:
{
lean_object* v_name_444_; 
v_name_444_ = lean_ctor_get(v_host_432_, 0);
lean_inc_ref(v_name_444_);
lean_dec_ref_known(v_host_432_, 1);
v___y_377_ = v___x_441_;
v___y_378_ = v_path_430_;
v_port_379_ = v_port_433_;
v___y_380_ = v_scheme_429_;
v___y_381_ = v___x_443_;
v___y_382_ = v___x_442_;
v___y_383_ = v___x_410_;
v___y_384_ = v_query_431_;
v___y_385_ = v___x_409_;
v___y_386_ = v_name_444_;
goto v___jp_376_;
}
case 1:
{
lean_object* v_ipv4_445_; lean_object* v___x_446_; 
v_ipv4_445_ = lean_ctor_get(v_host_432_, 0);
lean_inc_ref(v_ipv4_445_);
lean_dec_ref_known(v_host_432_, 1);
v___x_446_ = lean_uv_ntop_v4(v_ipv4_445_);
lean_dec_ref(v_ipv4_445_);
v___y_377_ = v___x_441_;
v___y_378_ = v_path_430_;
v_port_379_ = v_port_433_;
v___y_380_ = v_scheme_429_;
v___y_381_ = v___x_443_;
v___y_382_ = v___x_442_;
v___y_383_ = v___x_410_;
v___y_384_ = v_query_431_;
v___y_385_ = v___x_409_;
v___y_386_ = v___x_446_;
goto v___jp_376_;
}
case 2:
{
lean_object* v_ipv6_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_ipv6_447_ = lean_ctor_get(v_host_432_, 0);
lean_inc_ref(v_ipv6_447_);
lean_dec_ref_known(v_host_432_, 1);
v___x_448_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__19));
v___x_449_ = lean_uv_ntop_v6(v_ipv6_447_);
lean_dec_ref(v_ipv6_447_);
v___x_450_ = lean_string_append(v___x_448_, v___x_449_);
lean_dec_ref(v___x_449_);
v___x_451_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__20));
v___x_452_ = lean_string_append(v___x_450_, v___x_451_);
v___y_377_ = v___x_441_;
v___y_378_ = v_path_430_;
v_port_379_ = v_port_433_;
v___y_380_ = v_scheme_429_;
v___y_381_ = v___x_443_;
v___y_382_ = v___x_442_;
v___y_383_ = v___x_410_;
v___y_384_ = v_query_431_;
v___y_385_ = v___x_409_;
v___y_386_ = v___x_452_;
goto v___jp_376_;
}
default: 
{
v___y_377_ = v___x_441_;
v___y_378_ = v_path_430_;
v_port_379_ = v_port_433_;
v___y_380_ = v_scheme_429_;
v___y_381_ = v___x_443_;
v___y_382_ = v___x_442_;
v___y_383_ = v___x_410_;
v___y_384_ = v_query_431_;
v___y_385_ = v___x_409_;
v___y_386_ = v___x_443_;
goto v___jp_376_;
}
}
}
}
}
}
}
}
case 2:
{
lean_object* v_authority_458_; lean_object* v_host_459_; 
v_authority_458_ = lean_ctor_get(v_uri_304_, 0);
lean_inc_ref(v_authority_458_);
lean_dec_ref_known(v_uri_304_, 1);
v_host_459_ = lean_ctor_get(v_authority_458_, 1);
switch(lean_obj_tag(v_host_459_))
{
case 0:
{
lean_object* v_port_460_; lean_object* v_name_461_; 
lean_inc_ref(v_host_459_);
v_port_460_ = lean_ctor_get(v_authority_458_, 2);
lean_inc(v_port_460_);
lean_dec_ref(v_authority_458_);
v_name_461_ = lean_ctor_get(v_host_459_, 0);
lean_inc_ref(v_name_461_);
lean_dec_ref_known(v_host_459_, 1);
v___y_395_ = v_port_460_;
v___y_396_ = v___x_410_;
v___y_397_ = v___x_409_;
v___y_398_ = v_name_461_;
goto v___jp_394_;
}
case 1:
{
lean_object* v_port_462_; lean_object* v_ipv4_463_; lean_object* v___x_464_; 
lean_inc_ref(v_host_459_);
v_port_462_ = lean_ctor_get(v_authority_458_, 2);
lean_inc(v_port_462_);
lean_dec_ref(v_authority_458_);
v_ipv4_463_ = lean_ctor_get(v_host_459_, 0);
lean_inc_ref(v_ipv4_463_);
lean_dec_ref_known(v_host_459_, 1);
v___x_464_ = lean_uv_ntop_v4(v_ipv4_463_);
lean_dec_ref(v_ipv4_463_);
v___y_395_ = v_port_462_;
v___y_396_ = v___x_410_;
v___y_397_ = v___x_409_;
v___y_398_ = v___x_464_;
goto v___jp_394_;
}
case 2:
{
lean_object* v_port_465_; lean_object* v_ipv6_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_inc_ref(v_host_459_);
v_port_465_ = lean_ctor_get(v_authority_458_, 2);
lean_inc(v_port_465_);
lean_dec_ref(v_authority_458_);
v_ipv6_466_ = lean_ctor_get(v_host_459_, 0);
lean_inc_ref(v_ipv6_466_);
lean_dec_ref_known(v_host_459_, 1);
v___x_467_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__19));
v___x_468_ = lean_uv_ntop_v6(v_ipv6_466_);
lean_dec_ref(v_ipv6_466_);
v___x_469_ = lean_string_append(v___x_467_, v___x_468_);
lean_dec_ref(v___x_468_);
v___x_470_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__20));
v___x_471_ = lean_string_append(v___x_469_, v___x_470_);
v___y_395_ = v_port_465_;
v___y_396_ = v___x_410_;
v___y_397_ = v___x_409_;
v___y_398_ = v___x_471_;
goto v___jp_394_;
}
default: 
{
lean_object* v_port_472_; lean_object* v___x_473_; 
v_port_472_ = lean_ctor_get(v_authority_458_, 2);
lean_inc(v_port_472_);
lean_dec_ref(v_authority_458_);
v___x_473_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__3));
v___y_395_ = v_port_472_;
v___y_396_ = v___x_410_;
v___y_397_ = v___x_409_;
v___y_398_ = v___x_473_;
goto v___jp_394_;
}
}
}
default: 
{
lean_object* v___x_474_; 
v___x_474_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__21));
v___y_321_ = v___x_410_;
v___y_322_ = v___x_409_;
v___y_323_ = v___x_474_;
goto v___jp_320_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__0));
v___x_520_ = lean_string_to_utf8(v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0);
v___x_522_ = lean_byte_array_size(v___x_521_);
return v___x_522_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__11));
v___x_525_ = lean_string_to_utf8(v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3);
v___x_527_ = lean_byte_array_size(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__5(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__12));
v___x_529_ = lean_string_to_utf8(v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__6(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__5, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__5_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__5);
v___x_531_ = lean_byte_array_size(v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__7(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__13));
v___x_533_ = lean_string_to_utf8(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__8(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__7, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__7_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__7);
v___x_535_ = lean_byte_array_size(v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__9(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__14));
v___x_537_ = lean_string_to_utf8(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__10(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__9, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__9_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__9);
v___x_539_ = lean_byte_array_size(v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0(lean_object* v_out_540_, lean_object* v_req_541_){
_start:
{
uint8_t v_method_542_; uint8_t v_version_543_; lean_object* v_uri_544_; lean_object* v_headers_545_; lean_object* v___y_547_; lean_object* v___y_559_; uint8_t v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_594_; lean_object* v___y_595_; uint8_t v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_608_; lean_object* v___y_609_; uint8_t v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; uint8_t v___y_615_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; uint8_t v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; uint8_t v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v_port_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_660_; lean_object* v___y_661_; uint8_t v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_668_; 
v_method_542_ = lean_ctor_get_uint8(v_req_541_, sizeof(void*)*2);
v_version_543_ = lean_ctor_get_uint8(v_req_541_, sizeof(void*)*2 + 1);
v_uri_544_ = lean_ctor_get(v_req_541_, 0);
lean_inc(v_uri_544_);
v_headers_545_ = lean_ctor_get(v_req_541_, 1);
lean_inc_ref(v_headers_545_);
lean_dec_ref(v_req_541_);
switch(v_method_542_)
{
case 0:
{
lean_object* v___x_740_; 
v___x_740_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__22));
v___y_668_ = v___x_740_;
goto v___jp_667_;
}
case 1:
{
lean_object* v___x_741_; 
v___x_741_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__23));
v___y_668_ = v___x_741_;
goto v___jp_667_;
}
case 2:
{
lean_object* v___x_742_; 
v___x_742_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__24));
v___y_668_ = v___x_742_;
goto v___jp_667_;
}
case 3:
{
lean_object* v___x_743_; 
v___x_743_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__25));
v___y_668_ = v___x_743_;
goto v___jp_667_;
}
case 4:
{
lean_object* v___x_744_; 
v___x_744_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__26));
v___y_668_ = v___x_744_;
goto v___jp_667_;
}
case 5:
{
lean_object* v___x_745_; 
v___x_745_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__27));
v___y_668_ = v___x_745_;
goto v___jp_667_;
}
case 6:
{
lean_object* v___x_746_; 
v___x_746_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__28));
v___y_668_ = v___x_746_;
goto v___jp_667_;
}
case 7:
{
lean_object* v___x_747_; 
v___x_747_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__29));
v___y_668_ = v___x_747_;
goto v___jp_667_;
}
case 8:
{
lean_object* v___x_748_; 
v___x_748_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__30));
v___y_668_ = v___x_748_;
goto v___jp_667_;
}
case 9:
{
lean_object* v___x_749_; 
v___x_749_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__31));
v___y_668_ = v___x_749_;
goto v___jp_667_;
}
case 10:
{
lean_object* v___x_750_; 
v___x_750_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__32));
v___y_668_ = v___x_750_;
goto v___jp_667_;
}
case 11:
{
lean_object* v___x_751_; 
v___x_751_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__33));
v___y_668_ = v___x_751_;
goto v___jp_667_;
}
case 12:
{
lean_object* v___x_752_; 
v___x_752_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__34));
v___y_668_ = v___x_752_;
goto v___jp_667_;
}
case 13:
{
lean_object* v___x_753_; 
v___x_753_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__35));
v___y_668_ = v___x_753_;
goto v___jp_667_;
}
case 14:
{
lean_object* v___x_754_; 
v___x_754_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__36));
v___y_668_ = v___x_754_;
goto v___jp_667_;
}
case 15:
{
lean_object* v___x_755_; 
v___x_755_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__37));
v___y_668_ = v___x_755_;
goto v___jp_667_;
}
case 16:
{
lean_object* v___x_756_; 
v___x_756_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__38));
v___y_668_ = v___x_756_;
goto v___jp_667_;
}
case 17:
{
lean_object* v___x_757_; 
v___x_757_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__39));
v___y_668_ = v___x_757_;
goto v___jp_667_;
}
case 18:
{
lean_object* v___x_758_; 
v___x_758_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__40));
v___y_668_ = v___x_758_;
goto v___jp_667_;
}
case 19:
{
lean_object* v___x_759_; 
v___x_759_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__41));
v___y_668_ = v___x_759_;
goto v___jp_667_;
}
case 20:
{
lean_object* v___x_760_; 
v___x_760_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__42));
v___y_668_ = v___x_760_;
goto v___jp_667_;
}
case 21:
{
lean_object* v___x_761_; 
v___x_761_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__43));
v___y_668_ = v___x_761_;
goto v___jp_667_;
}
case 22:
{
lean_object* v___x_762_; 
v___x_762_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__44));
v___y_668_ = v___x_762_;
goto v___jp_667_;
}
case 23:
{
lean_object* v___x_763_; 
v___x_763_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__45));
v___y_668_ = v___x_763_;
goto v___jp_667_;
}
case 24:
{
lean_object* v___x_764_; 
v___x_764_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__46));
v___y_668_ = v___x_764_;
goto v___jp_667_;
}
case 25:
{
lean_object* v___x_765_; 
v___x_765_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__47));
v___y_668_ = v___x_765_;
goto v___jp_667_;
}
case 26:
{
lean_object* v___x_766_; 
v___x_766_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__48));
v___y_668_ = v___x_766_;
goto v___jp_667_;
}
case 27:
{
lean_object* v___x_767_; 
v___x_767_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__49));
v___y_668_ = v___x_767_;
goto v___jp_667_;
}
case 28:
{
lean_object* v___x_768_; 
v___x_768_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__50));
v___y_668_ = v___x_768_;
goto v___jp_667_;
}
case 29:
{
lean_object* v___x_769_; 
v___x_769_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__51));
v___y_668_ = v___x_769_;
goto v___jp_667_;
}
case 30:
{
lean_object* v___x_770_; 
v___x_770_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__52));
v___y_668_ = v___x_770_;
goto v___jp_667_;
}
case 31:
{
lean_object* v___x_771_; 
v___x_771_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__53));
v___y_668_ = v___x_771_;
goto v___jp_667_;
}
case 32:
{
lean_object* v___x_772_; 
v___x_772_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__54));
v___y_668_ = v___x_772_;
goto v___jp_667_;
}
case 33:
{
lean_object* v___x_773_; 
v___x_773_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__55));
v___y_668_ = v___x_773_;
goto v___jp_667_;
}
case 34:
{
lean_object* v___x_774_; 
v___x_774_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__56));
v___y_668_ = v___x_774_;
goto v___jp_667_;
}
case 35:
{
lean_object* v___x_775_; 
v___x_775_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__57));
v___y_668_ = v___x_775_;
goto v___jp_667_;
}
case 36:
{
lean_object* v___x_776_; 
v___x_776_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__58));
v___y_668_ = v___x_776_;
goto v___jp_667_;
}
case 37:
{
lean_object* v___x_777_; 
v___x_777_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__59));
v___y_668_ = v___x_777_;
goto v___jp_667_;
}
case 38:
{
lean_object* v___x_778_; 
v___x_778_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__60));
v___y_668_ = v___x_778_;
goto v___jp_667_;
}
default: 
{
lean_object* v___x_779_; 
v___x_779_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__61));
v___y_668_ = v___x_779_;
goto v___jp_667_;
}
}
v___jp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_548_ = lean_byte_array_size(v___y_547_);
v___x_549_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0);
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1);
v___x_552_ = 0;
v___x_553_ = lean_byte_array_copy_slice(v___x_549_, v___x_550_, v___y_547_, v___x_548_, v___x_551_, v___x_552_);
v___x_554_ = ((lean_object*)(l_Std_Http_Request_instEncodeV11Head___lam__0___closed__2));
v___x_555_ = l_Std_Http_Headers_fold___redArg(v_headers_545_, v___x_553_, v___x_554_);
lean_dec_ref(v_headers_545_);
v___x_556_ = lean_byte_array_size(v___x_555_);
v___x_557_ = lean_byte_array_copy_slice(v___x_549_, v___x_550_, v___x_555_, v___x_556_, v___x_551_, v___x_552_);
return v___x_557_;
}
v___jp_558_:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; 
v___x_563_ = lean_byte_array_size(v___y_559_);
v___x_564_ = lean_string_to_utf8(v___y_562_);
v___x_565_ = lean_byte_array_size(v___x_564_);
v___x_566_ = lean_byte_array_copy_slice(v___x_564_, v___y_561_, v___y_559_, v___x_563_, v___x_565_, v___y_560_);
lean_dec_ref(v___x_564_);
v___x_567_ = 32;
v___x_568_ = lean_byte_array_push(v___x_566_, v___x_567_);
switch(v_version_543_)
{
case 0:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; lean_object* v___x_574_; 
v___x_569_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3);
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_byte_array_size(v___x_568_);
v___x_572_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4);
v___x_573_ = 0;
v___x_574_ = lean_byte_array_copy_slice(v___x_569_, v___x_570_, v___x_568_, v___x_571_, v___x_572_, v___x_573_);
v___y_547_ = v___x_574_;
goto v___jp_546_;
}
case 1:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; lean_object* v___x_580_; 
v___x_575_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__5, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__5_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__5);
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = lean_byte_array_size(v___x_568_);
v___x_578_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__6, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__6_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__6);
v___x_579_ = 0;
v___x_580_ = lean_byte_array_copy_slice(v___x_575_, v___x_576_, v___x_568_, v___x_577_, v___x_578_, v___x_579_);
v___y_547_ = v___x_580_;
goto v___jp_546_;
}
case 2:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; 
v___x_581_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__7, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__7_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__7);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_byte_array_size(v___x_568_);
v___x_584_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__8, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__8_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__8);
v___x_585_ = 0;
v___x_586_ = lean_byte_array_copy_slice(v___x_581_, v___x_582_, v___x_568_, v___x_583_, v___x_584_, v___x_585_);
v___y_547_ = v___x_586_;
goto v___jp_546_;
}
default: 
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; lean_object* v___x_592_; 
v___x_587_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__9, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__9_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__9);
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = lean_byte_array_size(v___x_568_);
v___x_590_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__10, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__10_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__10);
v___x_591_ = 0;
v___x_592_ = lean_byte_array_copy_slice(v___x_587_, v___x_588_, v___x_568_, v___x_589_, v___x_590_, v___x_591_);
v___y_547_ = v___x_592_;
goto v___jp_546_;
}
}
}
v___jp_593_:
{
switch(lean_obj_tag(v___y_594_))
{
case 0:
{
v___y_559_ = v___y_595_;
v___y_560_ = v___y_596_;
v___y_561_ = v___y_597_;
v___y_562_ = v___y_598_;
goto v___jp_558_;
}
case 1:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___x_600_ = lean_string_append(v___y_598_, v___x_599_);
v___y_559_ = v___y_595_;
v___y_560_ = v___y_596_;
v___y_561_ = v___y_597_;
v___y_562_ = v___x_600_;
goto v___jp_558_;
}
default: 
{
uint16_t v_port_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_port_601_ = lean_ctor_get_uint16(v___y_594_, 0);
lean_dec_ref_known(v___y_594_, 0);
v___x_602_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___x_603_ = lean_uint16_to_nat(v_port_601_);
v___x_604_ = l_Nat_reprFast(v___x_603_);
v___x_605_ = lean_string_append(v___x_602_, v___x_604_);
lean_dec_ref(v___x_604_);
v___x_606_ = lean_string_append(v___y_598_, v___x_605_);
lean_dec_ref(v___x_605_);
v___y_559_ = v___y_595_;
v___y_560_ = v___y_596_;
v___y_561_ = v___y_597_;
v___y_562_ = v___x_606_;
goto v___jp_558_;
}
}
}
v___jp_607_:
{
uint8_t v___x_616_; lean_object* v_pathPart_617_; lean_object* v_queryPart_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_616_ = 1;
v_pathPart_617_ = l_Std_Http_URI_Path_render(v___y_613_, v___y_615_, v___x_616_);
v_queryPart_618_ = l_Std_Http_URI_Query_formatOption(v___y_609_);
v___x_619_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___x_620_ = lean_string_append(v___y_611_, v___x_619_);
v___x_621_ = lean_string_append(v___x_620_, v___y_612_);
lean_dec_ref(v___y_612_);
v___x_622_ = lean_string_append(v___x_621_, v_pathPart_617_);
lean_dec_ref(v_pathPart_617_);
v___x_623_ = lean_string_append(v___x_622_, v_queryPart_618_);
lean_dec_ref(v_queryPart_618_);
v___y_559_ = v___y_608_;
v___y_560_ = v___y_610_;
v___y_561_ = v___y_614_;
v___y_562_ = v___x_623_;
goto v___jp_558_;
}
v___jp_624_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
lean_dec(v___y_632_);
v___x_636_ = lean_string_append(v___y_633_, v___y_626_);
lean_dec_ref(v___y_626_);
v___x_637_ = lean_string_append(v___x_636_, v___y_635_);
lean_dec_ref(v___y_635_);
lean_inc_ref(v___y_625_);
v___x_638_ = lean_string_append(v___y_625_, v___x_637_);
lean_dec_ref(v___x_637_);
v___x_639_ = 1;
v___y_608_ = v___y_627_;
v___y_609_ = v___y_628_;
v___y_610_ = v___y_629_;
v___y_611_ = v___y_630_;
v___y_612_ = v___x_638_;
v___y_613_ = v___y_631_;
v___y_614_ = v___y_634_;
v___y_615_ = v___x_639_;
goto v___jp_607_;
}
v___jp_640_:
{
switch(lean_obj_tag(v_port_648_))
{
case 0:
{
lean_object* v___x_652_; 
v___x_652_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__3));
v___y_625_ = v___y_641_;
v___y_626_ = v___y_651_;
v___y_627_ = v___y_642_;
v___y_628_ = v___y_643_;
v___y_629_ = v___y_644_;
v___y_630_ = v___y_645_;
v___y_631_ = v___y_647_;
v___y_632_ = v___y_646_;
v___y_633_ = v___y_649_;
v___y_634_ = v___y_650_;
v___y_635_ = v___x_652_;
goto v___jp_624_;
}
case 1:
{
lean_object* v___x_653_; 
v___x_653_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___y_625_ = v___y_641_;
v___y_626_ = v___y_651_;
v___y_627_ = v___y_642_;
v___y_628_ = v___y_643_;
v___y_629_ = v___y_644_;
v___y_630_ = v___y_645_;
v___y_631_ = v___y_647_;
v___y_632_ = v___y_646_;
v___y_633_ = v___y_649_;
v___y_634_ = v___y_650_;
v___y_635_ = v___x_653_;
goto v___jp_624_;
}
default: 
{
uint16_t v_port_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_port_654_ = lean_ctor_get_uint16(v_port_648_, 0);
lean_dec_ref_known(v_port_648_, 0);
v___x_655_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___x_656_ = lean_uint16_to_nat(v_port_654_);
v___x_657_ = l_Nat_reprFast(v___x_656_);
v___x_658_ = lean_string_append(v___x_655_, v___x_657_);
lean_dec_ref(v___x_657_);
v___y_625_ = v___y_641_;
v___y_626_ = v___y_651_;
v___y_627_ = v___y_642_;
v___y_628_ = v___y_643_;
v___y_629_ = v___y_644_;
v___y_630_ = v___y_645_;
v___y_631_ = v___y_647_;
v___y_632_ = v___y_646_;
v___y_633_ = v___y_649_;
v___y_634_ = v___y_650_;
v___y_635_ = v___x_658_;
goto v___jp_624_;
}
}
}
v___jp_659_:
{
lean_object* v_queryStr_665_; lean_object* v___x_666_; 
v_queryStr_665_ = l_Std_Http_URI_Query_formatOption(v___y_661_);
v___x_666_ = lean_string_append(v___y_664_, v_queryStr_665_);
lean_dec_ref(v_queryStr_665_);
v___y_559_ = v___y_660_;
v___y_560_ = v___y_662_;
v___y_561_ = v___y_663_;
v___y_562_ = v___x_666_;
goto v___jp_558_;
}
v___jp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; lean_object* v___x_676_; 
v___x_669_ = lean_byte_array_size(v_out_540_);
lean_inc_ref(v___y_668_);
v___x_670_ = lean_string_to_utf8(v___y_668_);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_byte_array_size(v___x_670_);
v___x_673_ = 0;
v___x_674_ = lean_byte_array_copy_slice(v___x_670_, v___x_671_, v_out_540_, v___x_669_, v___x_672_, v___x_673_);
lean_dec_ref(v___x_670_);
v___x_675_ = 32;
v___x_676_ = lean_byte_array_push(v___x_674_, v___x_675_);
switch(lean_obj_tag(v_uri_544_))
{
case 0:
{
lean_object* v_path_677_; lean_object* v_query_678_; uint8_t v___x_679_; lean_object* v_pathStr_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_path_677_ = lean_ctor_get(v_uri_544_, 0);
lean_inc_ref(v_path_677_);
v_query_678_ = lean_ctor_get(v_uri_544_, 1);
lean_inc(v_query_678_);
lean_dec_ref_known(v_uri_544_, 2);
v___x_679_ = 1;
v_pathStr_680_ = l_Std_Http_URI_Path_render(v_path_677_, v___x_679_, v___x_679_);
v___x_681_ = lean_string_utf8_byte_size(v_pathStr_680_);
v___x_682_ = lean_nat_dec_eq(v___x_681_, v___x_671_);
if (v___x_682_ == 0)
{
v___y_660_ = v___x_676_;
v___y_661_ = v_query_678_;
v___y_662_ = v___x_673_;
v___y_663_ = v___x_671_;
v___y_664_ = v_pathStr_680_;
goto v___jp_659_;
}
else
{
lean_object* v___x_683_; 
lean_dec_ref(v_pathStr_680_);
v___x_683_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__17));
v___y_660_ = v___x_676_;
v___y_661_ = v_query_678_;
v___y_662_ = v___x_673_;
v___y_663_ = v___x_671_;
v___y_664_ = v___x_683_;
goto v___jp_659_;
}
}
case 1:
{
lean_object* v_uri_684_; lean_object* v_authority_685_; 
v_uri_684_ = lean_ctor_get(v_uri_544_, 0);
lean_inc_ref(v_uri_684_);
lean_dec_ref_known(v_uri_544_, 1);
v_authority_685_ = lean_ctor_get(v_uri_684_, 1);
lean_inc(v_authority_685_);
if (lean_obj_tag(v_authority_685_) == 0)
{
lean_object* v_scheme_686_; lean_object* v_path_687_; lean_object* v_query_688_; lean_object* v___x_689_; 
v_scheme_686_ = lean_ctor_get(v_uri_684_, 0);
lean_inc_ref(v_scheme_686_);
v_path_687_ = lean_ctor_get(v_uri_684_, 2);
lean_inc_ref(v_path_687_);
v_query_688_ = lean_ctor_get(v_uri_684_, 3);
lean_inc(v_query_688_);
lean_dec_ref(v_uri_684_);
v___x_689_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__3));
v___y_608_ = v___x_676_;
v___y_609_ = v_query_688_;
v___y_610_ = v___x_673_;
v___y_611_ = v_scheme_686_;
v___y_612_ = v___x_689_;
v___y_613_ = v_path_687_;
v___y_614_ = v___x_671_;
v___y_615_ = v___x_673_;
goto v___jp_607_;
}
else
{
lean_object* v_val_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_722_; 
v_val_690_ = lean_ctor_get(v_authority_685_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v_authority_685_);
if (v_isSharedCheck_722_ == 0)
{
v___x_692_ = v_authority_685_;
v_isShared_693_ = v_isSharedCheck_722_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_val_690_);
lean_dec(v_authority_685_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_722_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_scheme_694_; lean_object* v_path_695_; lean_object* v_query_696_; lean_object* v_host_697_; lean_object* v_port_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_720_; 
v_scheme_694_ = lean_ctor_get(v_uri_684_, 0);
lean_inc_ref(v_scheme_694_);
v_path_695_ = lean_ctor_get(v_uri_684_, 2);
lean_inc_ref(v_path_695_);
v_query_696_ = lean_ctor_get(v_uri_684_, 3);
lean_inc(v_query_696_);
lean_dec_ref(v_uri_684_);
v_host_697_ = lean_ctor_get(v_val_690_, 1);
v_port_698_ = lean_ctor_get(v_val_690_, 2);
v_isSharedCheck_720_ = !lean_is_exclusive(v_val_690_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v_val_690_, 0);
lean_dec(v_unused_721_);
v___x_700_ = v_val_690_;
v_isShared_701_ = v_isSharedCheck_720_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_port_698_);
lean_inc(v_host_697_);
lean_dec(v_val_690_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_720_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_702_ = lean_box(0);
lean_inc(v_port_698_);
lean_inc(v_host_697_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_702_);
v___x_704_ = v___x_700_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_host_697_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_port_698_);
v___x_704_ = v_reuseFailAlloc_719_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_706_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_704_);
v___x_706_ = v___x_692_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_718_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__18));
v___x_708_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__3));
switch(lean_obj_tag(v_host_697_))
{
case 0:
{
lean_object* v_name_709_; 
v_name_709_ = lean_ctor_get(v_host_697_, 0);
lean_inc_ref(v_name_709_);
lean_dec_ref_known(v_host_697_, 1);
v___y_641_ = v___x_707_;
v___y_642_ = v___x_676_;
v___y_643_ = v_query_696_;
v___y_644_ = v___x_673_;
v___y_645_ = v_scheme_694_;
v___y_646_ = v___x_706_;
v___y_647_ = v_path_695_;
v_port_648_ = v_port_698_;
v___y_649_ = v___x_708_;
v___y_650_ = v___x_671_;
v___y_651_ = v_name_709_;
goto v___jp_640_;
}
case 1:
{
lean_object* v_ipv4_710_; lean_object* v___x_711_; 
v_ipv4_710_ = lean_ctor_get(v_host_697_, 0);
lean_inc_ref(v_ipv4_710_);
lean_dec_ref_known(v_host_697_, 1);
v___x_711_ = lean_uv_ntop_v4(v_ipv4_710_);
lean_dec_ref(v_ipv4_710_);
v___y_641_ = v___x_707_;
v___y_642_ = v___x_676_;
v___y_643_ = v_query_696_;
v___y_644_ = v___x_673_;
v___y_645_ = v_scheme_694_;
v___y_646_ = v___x_706_;
v___y_647_ = v_path_695_;
v_port_648_ = v_port_698_;
v___y_649_ = v___x_708_;
v___y_650_ = v___x_671_;
v___y_651_ = v___x_711_;
goto v___jp_640_;
}
case 2:
{
lean_object* v_ipv6_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_ipv6_712_ = lean_ctor_get(v_host_697_, 0);
lean_inc_ref(v_ipv6_712_);
lean_dec_ref_known(v_host_697_, 1);
v___x_713_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__19));
v___x_714_ = lean_uv_ntop_v6(v_ipv6_712_);
lean_dec_ref(v_ipv6_712_);
v___x_715_ = lean_string_append(v___x_713_, v___x_714_);
lean_dec_ref(v___x_714_);
v___x_716_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__20));
v___x_717_ = lean_string_append(v___x_715_, v___x_716_);
v___y_641_ = v___x_707_;
v___y_642_ = v___x_676_;
v___y_643_ = v_query_696_;
v___y_644_ = v___x_673_;
v___y_645_ = v_scheme_694_;
v___y_646_ = v___x_706_;
v___y_647_ = v_path_695_;
v_port_648_ = v_port_698_;
v___y_649_ = v___x_708_;
v___y_650_ = v___x_671_;
v___y_651_ = v___x_717_;
goto v___jp_640_;
}
default: 
{
v___y_641_ = v___x_707_;
v___y_642_ = v___x_676_;
v___y_643_ = v_query_696_;
v___y_644_ = v___x_673_;
v___y_645_ = v_scheme_694_;
v___y_646_ = v___x_706_;
v___y_647_ = v_path_695_;
v_port_648_ = v_port_698_;
v___y_649_ = v___x_708_;
v___y_650_ = v___x_671_;
v___y_651_ = v___x_708_;
goto v___jp_640_;
}
}
}
}
}
}
}
}
case 2:
{
lean_object* v_authority_723_; lean_object* v_host_724_; 
v_authority_723_ = lean_ctor_get(v_uri_544_, 0);
lean_inc_ref(v_authority_723_);
lean_dec_ref_known(v_uri_544_, 1);
v_host_724_ = lean_ctor_get(v_authority_723_, 1);
switch(lean_obj_tag(v_host_724_))
{
case 0:
{
lean_object* v_port_725_; lean_object* v_name_726_; 
lean_inc_ref(v_host_724_);
v_port_725_ = lean_ctor_get(v_authority_723_, 2);
lean_inc(v_port_725_);
lean_dec_ref(v_authority_723_);
v_name_726_ = lean_ctor_get(v_host_724_, 0);
lean_inc_ref(v_name_726_);
lean_dec_ref_known(v_host_724_, 1);
v___y_594_ = v_port_725_;
v___y_595_ = v___x_676_;
v___y_596_ = v___x_673_;
v___y_597_ = v___x_671_;
v___y_598_ = v_name_726_;
goto v___jp_593_;
}
case 1:
{
lean_object* v_port_727_; lean_object* v_ipv4_728_; lean_object* v___x_729_; 
lean_inc_ref(v_host_724_);
v_port_727_ = lean_ctor_get(v_authority_723_, 2);
lean_inc(v_port_727_);
lean_dec_ref(v_authority_723_);
v_ipv4_728_ = lean_ctor_get(v_host_724_, 0);
lean_inc_ref(v_ipv4_728_);
lean_dec_ref_known(v_host_724_, 1);
v___x_729_ = lean_uv_ntop_v4(v_ipv4_728_);
lean_dec_ref(v_ipv4_728_);
v___y_594_ = v_port_727_;
v___y_595_ = v___x_676_;
v___y_596_ = v___x_673_;
v___y_597_ = v___x_671_;
v___y_598_ = v___x_729_;
goto v___jp_593_;
}
case 2:
{
lean_object* v_port_730_; lean_object* v_ipv6_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_inc_ref(v_host_724_);
v_port_730_ = lean_ctor_get(v_authority_723_, 2);
lean_inc(v_port_730_);
lean_dec_ref(v_authority_723_);
v_ipv6_731_ = lean_ctor_get(v_host_724_, 0);
lean_inc_ref(v_ipv6_731_);
lean_dec_ref_known(v_host_724_, 1);
v___x_732_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__19));
v___x_733_ = lean_uv_ntop_v6(v_ipv6_731_);
lean_dec_ref(v_ipv6_731_);
v___x_734_ = lean_string_append(v___x_732_, v___x_733_);
lean_dec_ref(v___x_733_);
v___x_735_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__20));
v___x_736_ = lean_string_append(v___x_734_, v___x_735_);
v___y_594_ = v_port_730_;
v___y_595_ = v___x_676_;
v___y_596_ = v___x_673_;
v___y_597_ = v___x_671_;
v___y_598_ = v___x_736_;
goto v___jp_593_;
}
default: 
{
lean_object* v_port_737_; lean_object* v___x_738_; 
v_port_737_ = lean_ctor_get(v_authority_723_, 2);
lean_inc(v_port_737_);
lean_dec_ref(v_authority_723_);
v___x_738_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__3));
v___y_594_ = v_port_737_;
v___y_595_ = v___x_676_;
v___y_596_ = v___x_673_;
v___y_597_ = v___x_671_;
v___y_598_ = v___x_738_;
goto v___jp_593_;
}
}
}
default: 
{
lean_object* v___x_739_; 
v___x_739_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__21));
v___y_559_ = v___x_676_;
v___y_560_ = v___x_673_;
v___y_561_ = v___x_671_;
v___y_562_ = v___x_739_;
goto v___jp_558_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__0(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; uint8_t v___x_785_; lean_object* v___x_786_; 
v___x_782_ = l_Std_Http_Headers_empty;
v___x_783_ = lean_box(3);
v___x_784_ = 1;
v___x_785_ = 8;
v___x_786_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_786_, 0, v___x_783_);
lean_ctor_set(v___x_786_, 1, v___x_782_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*2, v___x_785_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*2 + 1, v___x_784_);
return v___x_786_;
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__1(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_787_ = l_Std_Http_Extensions_empty;
v___x_788_ = lean_obj_once(&l_Std_Http_Request_new___closed__0, &l_Std_Http_Request_new___closed__0_once, _init_l_Std_Http_Request_new___closed__0);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v___x_787_);
return v___x_789_;
}
}
static lean_object* _init_l_Std_Http_Request_new(void){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = lean_obj_once(&l_Std_Http_Request_new___closed__1, &l_Std_Http_Request_new___closed__1_once, _init_l_Std_Http_Request_new___closed__1);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method(lean_object* v_builder_791_, uint8_t v_method_792_){
_start:
{
lean_object* v_line_793_; lean_object* v_extensions_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_811_; 
v_line_793_ = lean_ctor_get(v_builder_791_, 0);
v_extensions_794_ = lean_ctor_get(v_builder_791_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v_builder_791_);
if (v_isSharedCheck_811_ == 0)
{
v___x_796_ = v_builder_791_;
v_isShared_797_ = v_isSharedCheck_811_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_extensions_794_);
lean_inc(v_line_793_);
lean_dec(v_builder_791_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_811_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
uint8_t v_version_798_; lean_object* v_uri_799_; lean_object* v_headers_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_810_; 
v_version_798_ = lean_ctor_get_uint8(v_line_793_, sizeof(void*)*2 + 1);
v_uri_799_ = lean_ctor_get(v_line_793_, 0);
v_headers_800_ = lean_ctor_get(v_line_793_, 1);
v_isSharedCheck_810_ = !lean_is_exclusive(v_line_793_);
if (v_isSharedCheck_810_ == 0)
{
v___x_802_ = v_line_793_;
v_isShared_803_ = v_isSharedCheck_810_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_headers_800_);
lean_inc(v_uri_799_);
lean_dec(v_line_793_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_810_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_uri_799_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_headers_800_);
lean_ctor_set_uint8(v_reuseFailAlloc_809_, sizeof(void*)*2 + 1, v_version_798_);
v___x_805_ = v_reuseFailAlloc_809_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*2, v_method_792_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_805_);
v___x_807_ = v___x_796_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_extensions_794_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method___boxed(lean_object* v_builder_812_, lean_object* v_method_813_){
_start:
{
uint8_t v_method_boxed_814_; lean_object* v_res_815_; 
v_method_boxed_814_ = lean_unbox(v_method_813_);
v_res_815_ = l_Std_Http_Request_Builder_method(v_builder_812_, v_method_boxed_814_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version(lean_object* v_builder_816_, uint8_t v_version_817_){
_start:
{
lean_object* v_line_818_; lean_object* v_extensions_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_836_; 
v_line_818_ = lean_ctor_get(v_builder_816_, 0);
v_extensions_819_ = lean_ctor_get(v_builder_816_, 1);
v_isSharedCheck_836_ = !lean_is_exclusive(v_builder_816_);
if (v_isSharedCheck_836_ == 0)
{
v___x_821_ = v_builder_816_;
v_isShared_822_ = v_isSharedCheck_836_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_extensions_819_);
lean_inc(v_line_818_);
lean_dec(v_builder_816_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_836_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
uint8_t v_method_823_; lean_object* v_uri_824_; lean_object* v_headers_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_835_; 
v_method_823_ = lean_ctor_get_uint8(v_line_818_, sizeof(void*)*2);
v_uri_824_ = lean_ctor_get(v_line_818_, 0);
v_headers_825_ = lean_ctor_get(v_line_818_, 1);
v_isSharedCheck_835_ = !lean_is_exclusive(v_line_818_);
if (v_isSharedCheck_835_ == 0)
{
v___x_827_ = v_line_818_;
v_isShared_828_ = v_isSharedCheck_835_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_headers_825_);
lean_inc(v_uri_824_);
lean_dec(v_line_818_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_835_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_uri_824_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_headers_825_);
lean_ctor_set_uint8(v_reuseFailAlloc_834_, sizeof(void*)*2, v_method_823_);
v___x_830_ = v_reuseFailAlloc_834_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_832_; 
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*2 + 1, v_version_817_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_830_);
v___x_832_ = v___x_821_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_extensions_819_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version___boxed(lean_object* v_builder_837_, lean_object* v_version_838_){
_start:
{
uint8_t v_version_boxed_839_; lean_object* v_res_840_; 
v_version_boxed_839_ = lean_unbox(v_version_838_);
v_res_840_ = l_Std_Http_Request_Builder_version(v_builder_837_, v_version_boxed_839_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri(lean_object* v_builder_841_, lean_object* v_uri_842_){
_start:
{
lean_object* v_line_843_; lean_object* v_extensions_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_862_; 
v_line_843_ = lean_ctor_get(v_builder_841_, 0);
v_extensions_844_ = lean_ctor_get(v_builder_841_, 1);
v_isSharedCheck_862_ = !lean_is_exclusive(v_builder_841_);
if (v_isSharedCheck_862_ == 0)
{
v___x_846_ = v_builder_841_;
v_isShared_847_ = v_isSharedCheck_862_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_extensions_844_);
lean_inc(v_line_843_);
lean_dec(v_builder_841_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_862_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
uint8_t v_method_848_; uint8_t v_version_849_; lean_object* v_headers_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_860_; 
v_method_848_ = lean_ctor_get_uint8(v_line_843_, sizeof(void*)*2);
v_version_849_ = lean_ctor_get_uint8(v_line_843_, sizeof(void*)*2 + 1);
v_headers_850_ = lean_ctor_get(v_line_843_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v_line_843_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v_line_843_, 0);
lean_dec(v_unused_861_);
v___x_852_ = v_line_843_;
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_headers_850_);
lean_dec(v_line_843_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v_uri_842_);
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_uri_842_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_headers_850_);
lean_ctor_set_uint8(v_reuseFailAlloc_859_, sizeof(void*)*2, v_method_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_859_, sizeof(void*)*2 + 1, v_version_849_);
v___x_855_ = v_reuseFailAlloc_859_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_857_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_855_);
v___x_857_ = v___x_846_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_extensions_844_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(lean_object* v_msg_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = l_Std_Http_instInhabitedRequestTarget_default;
v___x_865_ = lean_panic_fn_borrowed(v___x_864_, v_msg_863_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___lam__0(lean_object* v___x_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_869_, v___y_870_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_pos_872_; lean_object* v_array_873_; lean_object* v_idx_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v_pos_872_ = lean_ctor_get(v___x_871_, 0);
v_array_873_ = lean_ctor_get(v_pos_872_, 0);
v_idx_874_ = lean_ctor_get(v_pos_872_, 1);
v___x_875_ = lean_byte_array_size(v_array_873_);
v___x_876_ = lean_nat_dec_lt(v_idx_874_, v___x_875_);
if (v___x_876_ == 0)
{
return v___x_871_;
}
else
{
lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_884_; 
lean_inc(v_pos_872_);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; lean_object* v_unused_886_; 
v_unused_885_ = lean_ctor_get(v___x_871_, 1);
lean_dec(v_unused_885_);
v_unused_886_ = lean_ctor_get(v___x_871_, 0);
lean_dec(v_unused_886_);
v___x_878_ = v___x_871_;
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
else
{
lean_dec(v___x_871_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_880_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___lam__0___closed__1));
if (v_isShared_879_ == 0)
{
lean_ctor_set_tag(v___x_878_, 1);
lean_ctor_set(v___x_878_, 1, v___x_880_);
v___x_882_ = v___x_878_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_pos_872_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
return v___x_871_;
}
}
}
static lean_object* _init_l_Std_Http_Request_Builder_uri_x21___closed__5(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_897_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__4));
v___x_898_ = lean_unsigned_to_nat(12u);
v___x_899_ = lean_unsigned_to_nat(45u);
v___x_900_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__3));
v___x_901_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__2));
v___x_902_ = l_mkPanicMessageWithDecl(v___x_901_, v___x_900_, v___x_899_, v___x_898_, v___x_897_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21(lean_object* v_builder_903_, lean_object* v_uri_904_){
_start:
{
lean_object* v___y_906_; lean_object* v___f_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___f_927_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__1));
v___x_928_ = lean_string_to_utf8(v_uri_904_);
v___x_929_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_927_, v___x_928_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec_ref_known(v___x_929_, 1);
v___x_930_ = lean_obj_once(&l_Std_Http_Request_Builder_uri_x21___closed__5, &l_Std_Http_Request_Builder_uri_x21___closed__5_once, _init_l_Std_Http_Request_Builder_uri_x21___closed__5);
v___x_931_ = l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(v___x_930_);
v___y_906_ = v___x_931_;
goto v___jp_905_;
}
else
{
lean_object* v_a_932_; 
v_a_932_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_929_, 1);
v___y_906_ = v_a_932_;
goto v___jp_905_;
}
v___jp_905_:
{
lean_object* v_line_907_; lean_object* v_extensions_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_926_; 
v_line_907_ = lean_ctor_get(v_builder_903_, 0);
v_extensions_908_ = lean_ctor_get(v_builder_903_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_builder_903_);
if (v_isSharedCheck_926_ == 0)
{
v___x_910_ = v_builder_903_;
v_isShared_911_ = v_isSharedCheck_926_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_extensions_908_);
lean_inc(v_line_907_);
lean_dec(v_builder_903_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_926_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
uint8_t v_method_912_; uint8_t v_version_913_; lean_object* v_headers_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_924_; 
v_method_912_ = lean_ctor_get_uint8(v_line_907_, sizeof(void*)*2);
v_version_913_ = lean_ctor_get_uint8(v_line_907_, sizeof(void*)*2 + 1);
v_headers_914_ = lean_ctor_get(v_line_907_, 1);
v_isSharedCheck_924_ = !lean_is_exclusive(v_line_907_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; 
v_unused_925_ = lean_ctor_get(v_line_907_, 0);
lean_dec(v_unused_925_);
v___x_916_ = v_line_907_;
v_isShared_917_ = v_isSharedCheck_924_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_headers_914_);
lean_dec(v_line_907_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_924_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___y_906_);
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___y_906_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_headers_914_);
lean_ctor_set_uint8(v_reuseFailAlloc_923_, sizeof(void*)*2, v_method_912_);
lean_ctor_set_uint8(v_reuseFailAlloc_923_, sizeof(void*)*2 + 1, v_version_913_);
v___x_919_ = v_reuseFailAlloc_923_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_921_; 
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_919_);
v___x_921_ = v___x_910_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_extensions_908_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headers(lean_object* v_builder_933_, lean_object* v_headers_934_){
_start:
{
lean_object* v_line_935_; lean_object* v_extensions_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_954_; 
v_line_935_ = lean_ctor_get(v_builder_933_, 0);
v_extensions_936_ = lean_ctor_get(v_builder_933_, 1);
v_isSharedCheck_954_ = !lean_is_exclusive(v_builder_933_);
if (v_isSharedCheck_954_ == 0)
{
v___x_938_ = v_builder_933_;
v_isShared_939_ = v_isSharedCheck_954_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_extensions_936_);
lean_inc(v_line_935_);
lean_dec(v_builder_933_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_954_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
uint8_t v_method_940_; uint8_t v_version_941_; lean_object* v_uri_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_952_; 
v_method_940_ = lean_ctor_get_uint8(v_line_935_, sizeof(void*)*2);
v_version_941_ = lean_ctor_get_uint8(v_line_935_, sizeof(void*)*2 + 1);
v_uri_942_ = lean_ctor_get(v_line_935_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v_line_935_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; 
v_unused_953_ = lean_ctor_get(v_line_935_, 1);
lean_dec(v_unused_953_);
v___x_944_ = v_line_935_;
v_isShared_945_ = v_isSharedCheck_952_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_uri_942_);
lean_dec(v_line_935_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_952_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v_headers_934_);
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_uri_942_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_headers_934_);
lean_ctor_set_uint8(v_reuseFailAlloc_951_, sizeof(void*)*2, v_method_940_);
lean_ctor_set_uint8(v_reuseFailAlloc_951_, sizeof(void*)*2 + 1, v_version_941_);
v___x_947_ = v_reuseFailAlloc_951_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_949_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_947_);
v___x_949_ = v___x_938_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_extensions_936_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header(lean_object* v_builder_955_, lean_object* v_key_956_, lean_object* v_value_957_){
_start:
{
lean_object* v_line_958_; lean_object* v_extensions_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_979_; 
v_line_958_ = lean_ctor_get(v_builder_955_, 0);
v_extensions_959_ = lean_ctor_get(v_builder_955_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v_builder_955_);
if (v_isSharedCheck_979_ == 0)
{
v___x_961_ = v_builder_955_;
v_isShared_962_ = v_isSharedCheck_979_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_extensions_959_);
lean_inc(v_line_958_);
lean_dec(v_builder_955_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_979_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
uint8_t v_method_963_; uint8_t v_version_964_; lean_object* v_uri_965_; lean_object* v_headers_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_978_; 
v_method_963_ = lean_ctor_get_uint8(v_line_958_, sizeof(void*)*2);
v_version_964_ = lean_ctor_get_uint8(v_line_958_, sizeof(void*)*2 + 1);
v_uri_965_ = lean_ctor_get(v_line_958_, 0);
v_headers_966_ = lean_ctor_get(v_line_958_, 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v_line_958_);
if (v_isSharedCheck_978_ == 0)
{
v___x_968_ = v_line_958_;
v_isShared_969_ = v_isSharedCheck_978_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_headers_966_);
lean_inc(v_uri_965_);
lean_dec(v_line_958_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_978_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v_key_956_);
lean_ctor_set(v___x_970_, 1, v_value_957_);
v___x_971_ = lean_array_push(v_headers_966_, v___x_970_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 1, v___x_971_);
v___x_973_ = v___x_968_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_uri_965_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v___x_971_);
lean_ctor_set_uint8(v_reuseFailAlloc_977_, sizeof(void*)*2, v_method_963_);
lean_ctor_set_uint8(v_reuseFailAlloc_977_, sizeof(void*)*2 + 1, v_version_964_);
v___x_973_ = v_reuseFailAlloc_977_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_975_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_973_);
v___x_975_ = v___x_961_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_extensions_959_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x21(lean_object* v_builder_980_, lean_object* v_key_981_, lean_object* v_value_982_){
_start:
{
lean_object* v_line_983_; lean_object* v_extensions_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1006_; 
v_line_983_ = lean_ctor_get(v_builder_980_, 0);
v_extensions_984_ = lean_ctor_get(v_builder_980_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_builder_980_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_986_ = v_builder_980_;
v_isShared_987_ = v_isSharedCheck_1006_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_extensions_984_);
lean_inc(v_line_983_);
lean_dec(v_builder_980_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1006_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
uint8_t v_method_988_; uint8_t v_version_989_; lean_object* v_uri_990_; lean_object* v_headers_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1005_; 
v_method_988_ = lean_ctor_get_uint8(v_line_983_, sizeof(void*)*2);
v_version_989_ = lean_ctor_get_uint8(v_line_983_, sizeof(void*)*2 + 1);
v_uri_990_ = lean_ctor_get(v_line_983_, 0);
v_headers_991_ = lean_ctor_get(v_line_983_, 1);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_line_983_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_993_ = v_line_983_;
v_isShared_994_ = v_isSharedCheck_1005_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_headers_991_);
lean_inc(v_uri_990_);
lean_dec(v_line_983_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1005_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v_key_995_; lean_object* v_value_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v_key_995_ = l_Std_Http_Header_Name_ofString_x21(v_key_981_);
v_value_996_ = l_Std_Http_Header_Value_ofString_x21(v_value_982_);
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v_key_995_);
lean_ctor_set(v___x_997_, 1, v_value_996_);
v___x_998_ = lean_array_push(v_headers_991_, v___x_997_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v___x_998_);
v___x_1000_ = v___x_993_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_uri_990_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v___x_998_);
lean_ctor_set_uint8(v_reuseFailAlloc_1004_, sizeof(void*)*2, v_method_988_);
lean_ctor_set_uint8(v_reuseFailAlloc_1004_, sizeof(void*)*2 + 1, v_version_989_);
v___x_1000_ = v_reuseFailAlloc_1004_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1002_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_1000_);
v___x_1002_ = v___x_986_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_extensions_984_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x3f(lean_object* v_builder_1007_, lean_object* v_key_1008_, lean_object* v_value_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Std_Http_Header_Name_ofString_x3f(v_key_1008_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v___x_1011_; 
lean_dec_ref(v_value_1009_);
lean_dec_ref(v_builder_1007_);
v___x_1011_ = lean_box(0);
return v___x_1011_;
}
else
{
lean_object* v_val_1012_; lean_object* v___x_1013_; 
v_val_1012_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_val_1012_);
lean_dec_ref_known(v___x_1010_, 1);
v___x_1013_ = l_Std_Http_Header_Value_ofString_x3f(v_value_1009_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v___x_1014_; 
lean_dec(v_val_1012_);
lean_dec_ref(v_builder_1007_);
v___x_1014_ = lean_box(0);
return v___x_1014_;
}
else
{
lean_object* v_line_1015_; lean_object* v_val_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1045_; 
v_line_1015_ = lean_ctor_get(v_builder_1007_, 0);
lean_inc_ref(v_line_1015_);
v_val_1016_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1018_ = v___x_1013_;
v_isShared_1019_ = v_isSharedCheck_1045_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_val_1016_);
lean_dec(v___x_1013_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1045_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v_extensions_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1043_; 
v_extensions_1020_ = lean_ctor_get(v_builder_1007_, 1);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_builder_1007_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v_builder_1007_, 0);
lean_dec(v_unused_1044_);
v___x_1022_ = v_builder_1007_;
v_isShared_1023_ = v_isSharedCheck_1043_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_extensions_1020_);
lean_dec(v_builder_1007_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1043_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
uint8_t v_method_1024_; uint8_t v_version_1025_; lean_object* v_uri_1026_; lean_object* v_headers_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1042_; 
v_method_1024_ = lean_ctor_get_uint8(v_line_1015_, sizeof(void*)*2);
v_version_1025_ = lean_ctor_get_uint8(v_line_1015_, sizeof(void*)*2 + 1);
v_uri_1026_ = lean_ctor_get(v_line_1015_, 0);
v_headers_1027_ = lean_ctor_get(v_line_1015_, 1);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_line_1015_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1029_ = v_line_1015_;
v_isShared_1030_ = v_isSharedCheck_1042_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_headers_1027_);
lean_inc(v_uri_1026_);
lean_dec(v_line_1015_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1042_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v_val_1012_);
lean_ctor_set(v___x_1031_, 1, v_val_1016_);
v___x_1032_ = lean_array_push(v_headers_1027_, v___x_1031_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 1, v___x_1032_);
v___x_1034_ = v___x_1029_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_uri_1026_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v___x_1032_);
lean_ctor_set_uint8(v_reuseFailAlloc_1041_, sizeof(void*)*2, v_method_1024_);
lean_ctor_set_uint8(v_reuseFailAlloc_1041_, sizeof(void*)*2 + 1, v_version_1025_);
v___x_1034_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1036_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1034_);
v___x_1036_ = v___x_1022_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_extensions_1020_);
v___x_1036_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1036_);
v___x_1038_ = v___x_1018_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
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
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headerOpt(lean_object* v_builder_1046_, lean_object* v_key_1047_, lean_object* v_value_1048_){
_start:
{
if (lean_obj_tag(v_value_1048_) == 0)
{
lean_dec_ref(v_key_1047_);
return v_builder_1046_;
}
else
{
lean_object* v_val_1049_; lean_object* v___x_1050_; 
v_val_1049_ = lean_ctor_get(v_value_1048_, 0);
lean_inc(v_val_1049_);
lean_dec_ref_known(v_value_1048_, 1);
v___x_1050_ = l_Std_Http_Request_Builder_header(v_builder_1046_, v_key_1047_, v_val_1049_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension___redArg(lean_object* v_builder_1052_, lean_object* v_inst_1053_, lean_object* v_data_1054_){
_start:
{
lean_object* v_line_1055_; lean_object* v_extensions_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1067_; 
v_line_1055_ = lean_ctor_get(v_builder_1052_, 0);
v_extensions_1056_ = lean_ctor_get(v_builder_1052_, 1);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_builder_1052_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1058_ = v_builder_1052_;
v_isShared_1059_ = v_isSharedCheck_1067_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_extensions_1056_);
lean_inc(v_line_1055_);
lean_dec(v_builder_1052_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1067_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v_dyn_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
v_dyn_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_1060_, 0, v_inst_1053_);
lean_ctor_set(v_dyn_1060_, 1, v_data_1054_);
v___x_1061_ = ((lean_object*)(l_Std_Http_Request_Builder_extension___redArg___closed__0));
v___x_1062_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_1060_);
v___x_1063_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1061_, v___x_1062_, v_dyn_1060_, v_extensions_1056_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v___x_1063_);
v___x_1065_ = v___x_1058_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_line_1055_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension(lean_object* v_00_u03b1_1068_, lean_object* v_builder_1069_, lean_object* v_inst_1070_, lean_object* v_data_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Std_Http_Request_Builder_extension___redArg(v_builder_1069_, v_inst_1070_, v_data_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object* v_builder_1073_, lean_object* v_body_1074_){
_start:
{
lean_object* v_line_1075_; lean_object* v_extensions_1076_; lean_object* v___x_1077_; 
v_line_1075_ = lean_ctor_get(v_builder_1073_, 0);
v_extensions_1076_ = lean_ctor_get(v_builder_1073_, 1);
lean_inc(v_extensions_1076_);
lean_inc_ref(v_line_1075_);
v___x_1077_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1077_, 0, v_line_1075_);
lean_ctor_set(v___x_1077_, 1, v_body_1074_);
lean_ctor_set(v___x_1077_, 2, v_extensions_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg___boxed(lean_object* v_builder_1078_, lean_object* v_body_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1078_, v_body_1079_);
lean_dec_ref(v_builder_1078_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body(lean_object* v_t_1081_, lean_object* v_builder_1082_, lean_object* v_body_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1082_, v_body_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___boxed(lean_object* v_t_1085_, lean_object* v_builder_1086_, lean_object* v_body_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Std_Http_Request_Builder_body(v_t_1085_, v_builder_1086_, v_body_1087_);
lean_dec_ref(v_builder_1086_);
return v_res_1088_;
}
}
static lean_object* _init_l_Std_Http_Request_get___closed__0(void){
_start:
{
uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = 8;
v___x_1090_ = l_Std_Http_Request_new;
v___x_1091_ = l_Std_Http_Request_Builder_method(v___x_1090_, v___x_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_get(lean_object* v_uri_1092_){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_obj_once(&l_Std_Http_Request_get___closed__0, &l_Std_Http_Request_get___closed__0_once, _init_l_Std_Http_Request_get___closed__0);
v___x_1094_ = l_Std_Http_Request_Builder_uri(v___x_1093_, v_uri_1092_);
return v___x_1094_;
}
}
static lean_object* _init_l_Std_Http_Request_post___closed__0(void){
_start:
{
uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1095_ = 23;
v___x_1096_ = l_Std_Http_Request_new;
v___x_1097_ = l_Std_Http_Request_Builder_method(v___x_1096_, v___x_1095_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_post(lean_object* v_uri_1098_){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = lean_obj_once(&l_Std_Http_Request_post___closed__0, &l_Std_Http_Request_post___closed__0_once, _init_l_Std_Http_Request_post___closed__0);
v___x_1100_ = l_Std_Http_Request_Builder_uri(v___x_1099_, v_uri_1098_);
return v___x_1100_;
}
}
static lean_object* _init_l_Std_Http_Request_put___closed__0(void){
_start:
{
uint8_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = 27;
v___x_1102_ = l_Std_Http_Request_new;
v___x_1103_ = l_Std_Http_Request_Builder_method(v___x_1102_, v___x_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_put(lean_object* v_uri_1104_){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_obj_once(&l_Std_Http_Request_put___closed__0, &l_Std_Http_Request_put___closed__0_once, _init_l_Std_Http_Request_put___closed__0);
v___x_1106_ = l_Std_Http_Request_Builder_uri(v___x_1105_, v_uri_1104_);
return v___x_1106_;
}
}
static lean_object* _init_l_Std_Http_Request_delete___closed__0(void){
_start:
{
uint8_t v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = 7;
v___x_1108_ = l_Std_Http_Request_new;
v___x_1109_ = l_Std_Http_Request_Builder_method(v___x_1108_, v___x_1107_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_delete(lean_object* v_uri_1110_){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_obj_once(&l_Std_Http_Request_delete___closed__0, &l_Std_Http_Request_delete___closed__0_once, _init_l_Std_Http_Request_delete___closed__0);
v___x_1112_ = l_Std_Http_Request_Builder_uri(v___x_1111_, v_uri_1110_);
return v___x_1112_;
}
}
static lean_object* _init_l_Std_Http_Request_patch___closed__0(void){
_start:
{
uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = 22;
v___x_1114_ = l_Std_Http_Request_new;
v___x_1115_ = l_Std_Http_Request_Builder_method(v___x_1114_, v___x_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_patch(lean_object* v_uri_1116_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_obj_once(&l_Std_Http_Request_patch___closed__0, &l_Std_Http_Request_patch___closed__0_once, _init_l_Std_Http_Request_patch___closed__0);
v___x_1118_ = l_Std_Http_Request_Builder_uri(v___x_1117_, v_uri_1116_);
return v___x_1118_;
}
}
static lean_object* _init_l_Std_Http_Request_head___closed__0(void){
_start:
{
uint8_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = 9;
v___x_1120_ = l_Std_Http_Request_new;
v___x_1121_ = l_Std_Http_Request_Builder_method(v___x_1120_, v___x_1119_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_head(lean_object* v_uri_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_obj_once(&l_Std_Http_Request_head___closed__0, &l_Std_Http_Request_head___closed__0_once, _init_l_Std_Http_Request_head___closed__0);
v___x_1124_ = l_Std_Http_Request_Builder_uri(v___x_1123_, v_uri_1122_);
return v___x_1124_;
}
}
static lean_object* _init_l_Std_Http_Request_options___closed__0(void){
_start:
{
uint8_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = 20;
v___x_1126_ = l_Std_Http_Request_new;
v___x_1127_ = l_Std_Http_Request_Builder_method(v___x_1126_, v___x_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_options(lean_object* v_uri_1128_){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_obj_once(&l_Std_Http_Request_options___closed__0, &l_Std_Http_Request_options___closed__0_once, _init_l_Std_Http_Request_options___closed__0);
v___x_1130_ = l_Std_Http_Request_Builder_uri(v___x_1129_, v_uri_1128_);
return v___x_1130_;
}
}
static lean_object* _init_l_Std_Http_Request_connect___closed__0(void){
_start:
{
uint8_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1131_ = 5;
v___x_1132_ = l_Std_Http_Request_new;
v___x_1133_ = l_Std_Http_Request_Builder_method(v___x_1132_, v___x_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_connect(lean_object* v_uri_1134_){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_obj_once(&l_Std_Http_Request_connect___closed__0, &l_Std_Http_Request_connect___closed__0_once, _init_l_Std_Http_Request_connect___closed__0);
v___x_1136_ = l_Std_Http_Request_Builder_uri(v___x_1135_, v_uri_1134_);
return v___x_1136_;
}
}
static lean_object* _init_l_Std_Http_Request_trace___closed__0(void){
_start:
{
uint8_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = 32;
v___x_1138_ = l_Std_Http_Request_new;
v___x_1139_ = l_Std_Http_Request_Builder_method(v___x_1138_, v___x_1137_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_trace(lean_object* v_uri_1140_){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_obj_once(&l_Std_Http_Request_trace___closed__0, &l_Std_Http_Request_trace___closed__0_once, _init_l_Std_Http_Request_trace___closed__0);
v___x_1142_ = l_Std_Http_Request_Builder_uri(v___x_1141_, v_uri_1140_);
return v___x_1142_;
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
l_Std_Http_Request_instToStringHead___lam__1___boxed__const__1 = _init_l_Std_Http_Request_instToStringHead___lam__1___boxed__const__1();
lean_mark_persistent(l_Std_Http_Request_instToStringHead___lam__1___boxed__const__1);
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
