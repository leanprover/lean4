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
uint32_t v___x_1387__boxed_200_; lean_object* v_res_201_; 
v___x_1387__boxed_200_ = lean_unbox_uint32(v___x_194_);
lean_dec(v___x_194_);
v_res_201_ = l_Std_Http_Request_instToStringHead___lam__0(v___x_189_, v___x_190_, v___x_191_, v_fst_192_, v___x_193_, v___x_1387__boxed_200_, v___x_195_, v_it_196_, v_acc_197_, v_hP_198_, v_recur_199_);
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
uint8_t v_method_302_; uint8_t v_version_303_; lean_object* v_uri_304_; lean_object* v_headers_305_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; uint8_t v___y_344_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v_port_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_408_; 
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
lean_object* v___x_473_; 
v___x_473_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__22));
v___y_408_ = v___x_473_;
goto v___jp_407_;
}
case 1:
{
lean_object* v___x_474_; 
v___x_474_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__23));
v___y_408_ = v___x_474_;
goto v___jp_407_;
}
case 2:
{
lean_object* v___x_475_; 
v___x_475_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__24));
v___y_408_ = v___x_475_;
goto v___jp_407_;
}
case 3:
{
lean_object* v___x_476_; 
v___x_476_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__25));
v___y_408_ = v___x_476_;
goto v___jp_407_;
}
case 4:
{
lean_object* v___x_477_; 
v___x_477_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__26));
v___y_408_ = v___x_477_;
goto v___jp_407_;
}
case 5:
{
lean_object* v___x_478_; 
v___x_478_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__27));
v___y_408_ = v___x_478_;
goto v___jp_407_;
}
case 6:
{
lean_object* v___x_479_; 
v___x_479_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__28));
v___y_408_ = v___x_479_;
goto v___jp_407_;
}
case 7:
{
lean_object* v___x_480_; 
v___x_480_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__29));
v___y_408_ = v___x_480_;
goto v___jp_407_;
}
case 8:
{
lean_object* v___x_481_; 
v___x_481_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__30));
v___y_408_ = v___x_481_;
goto v___jp_407_;
}
case 9:
{
lean_object* v___x_482_; 
v___x_482_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__31));
v___y_408_ = v___x_482_;
goto v___jp_407_;
}
case 10:
{
lean_object* v___x_483_; 
v___x_483_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__32));
v___y_408_ = v___x_483_;
goto v___jp_407_;
}
case 11:
{
lean_object* v___x_484_; 
v___x_484_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__33));
v___y_408_ = v___x_484_;
goto v___jp_407_;
}
case 12:
{
lean_object* v___x_485_; 
v___x_485_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__34));
v___y_408_ = v___x_485_;
goto v___jp_407_;
}
case 13:
{
lean_object* v___x_486_; 
v___x_486_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__35));
v___y_408_ = v___x_486_;
goto v___jp_407_;
}
case 14:
{
lean_object* v___x_487_; 
v___x_487_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__36));
v___y_408_ = v___x_487_;
goto v___jp_407_;
}
case 15:
{
lean_object* v___x_488_; 
v___x_488_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__37));
v___y_408_ = v___x_488_;
goto v___jp_407_;
}
case 16:
{
lean_object* v___x_489_; 
v___x_489_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__38));
v___y_408_ = v___x_489_;
goto v___jp_407_;
}
case 17:
{
lean_object* v___x_490_; 
v___x_490_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__39));
v___y_408_ = v___x_490_;
goto v___jp_407_;
}
case 18:
{
lean_object* v___x_491_; 
v___x_491_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__40));
v___y_408_ = v___x_491_;
goto v___jp_407_;
}
case 19:
{
lean_object* v___x_492_; 
v___x_492_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__41));
v___y_408_ = v___x_492_;
goto v___jp_407_;
}
case 20:
{
lean_object* v___x_493_; 
v___x_493_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__42));
v___y_408_ = v___x_493_;
goto v___jp_407_;
}
case 21:
{
lean_object* v___x_494_; 
v___x_494_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__43));
v___y_408_ = v___x_494_;
goto v___jp_407_;
}
case 22:
{
lean_object* v___x_495_; 
v___x_495_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__44));
v___y_408_ = v___x_495_;
goto v___jp_407_;
}
case 23:
{
lean_object* v___x_496_; 
v___x_496_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__45));
v___y_408_ = v___x_496_;
goto v___jp_407_;
}
case 24:
{
lean_object* v___x_497_; 
v___x_497_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__46));
v___y_408_ = v___x_497_;
goto v___jp_407_;
}
case 25:
{
lean_object* v___x_498_; 
v___x_498_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__47));
v___y_408_ = v___x_498_;
goto v___jp_407_;
}
case 26:
{
lean_object* v___x_499_; 
v___x_499_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__48));
v___y_408_ = v___x_499_;
goto v___jp_407_;
}
case 27:
{
lean_object* v___x_500_; 
v___x_500_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__49));
v___y_408_ = v___x_500_;
goto v___jp_407_;
}
case 28:
{
lean_object* v___x_501_; 
v___x_501_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__50));
v___y_408_ = v___x_501_;
goto v___jp_407_;
}
case 29:
{
lean_object* v___x_502_; 
v___x_502_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__51));
v___y_408_ = v___x_502_;
goto v___jp_407_;
}
case 30:
{
lean_object* v___x_503_; 
v___x_503_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__52));
v___y_408_ = v___x_503_;
goto v___jp_407_;
}
case 31:
{
lean_object* v___x_504_; 
v___x_504_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__53));
v___y_408_ = v___x_504_;
goto v___jp_407_;
}
case 32:
{
lean_object* v___x_505_; 
v___x_505_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__54));
v___y_408_ = v___x_505_;
goto v___jp_407_;
}
case 33:
{
lean_object* v___x_506_; 
v___x_506_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__55));
v___y_408_ = v___x_506_;
goto v___jp_407_;
}
case 34:
{
lean_object* v___x_507_; 
v___x_507_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__56));
v___y_408_ = v___x_507_;
goto v___jp_407_;
}
case 35:
{
lean_object* v___x_508_; 
v___x_508_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__57));
v___y_408_ = v___x_508_;
goto v___jp_407_;
}
case 36:
{
lean_object* v___x_509_; 
v___x_509_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__58));
v___y_408_ = v___x_509_;
goto v___jp_407_;
}
case 37:
{
lean_object* v___x_510_; 
v___x_510_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__59));
v___y_408_ = v___x_510_;
goto v___jp_407_;
}
case 38:
{
lean_object* v___x_511_; 
v___x_511_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__60));
v___y_408_ = v___x_511_;
goto v___jp_407_;
}
default: 
{
lean_object* v___x_512_; 
v___x_512_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__61));
v___y_408_ = v___x_512_;
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
v_queryStr_335_ = l_Std_Http_URI_Query_formatOption(v___y_331_);
v___x_336_ = lean_string_append(v___y_334_, v_queryStr_335_);
lean_dec_ref(v_queryStr_335_);
v___y_321_ = v___y_332_;
v___y_322_ = v___y_333_;
v___y_323_ = v___x_336_;
goto v___jp_320_;
}
v___jp_337_:
{
uint8_t v___x_345_; lean_object* v_pathPart_346_; lean_object* v_queryPart_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_345_ = 1;
v_pathPart_346_ = l_Std_Http_URI_Path_render(v___y_340_, v___y_344_, v___x_345_);
v_queryPart_347_ = l_Std_Http_URI_Query_formatOption(v___y_338_);
v___x_348_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___x_349_ = lean_string_append(v___y_339_, v___x_348_);
v___x_350_ = lean_string_append(v___x_349_, v___y_342_);
lean_dec_ref(v___y_342_);
v___x_351_ = lean_string_append(v___x_350_, v_pathPart_346_);
lean_dec_ref(v_pathPart_346_);
v___x_352_ = lean_string_append(v___x_351_, v_queryPart_347_);
lean_dec_ref(v_queryPart_347_);
v___y_321_ = v___y_341_;
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
v___y_341_ = v___y_357_;
v___y_342_ = v___y_359_;
v___y_343_ = v___y_358_;
v___y_344_ = v___x_360_;
goto v___jp_337_;
}
v___jp_361_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
lean_dec(v___y_368_);
lean_inc_ref(v___y_364_);
v___x_372_ = lean_string_append(v___y_364_, v___y_365_);
lean_dec_ref(v___y_365_);
v___x_373_ = lean_string_append(v___x_372_, v___y_371_);
lean_dec_ref(v___y_371_);
lean_inc_ref(v___y_369_);
v___x_374_ = lean_string_append(v___y_369_, v___x_373_);
lean_dec_ref(v___x_373_);
v___x_375_ = 1;
v___y_338_ = v___y_362_;
v___y_339_ = v___y_363_;
v___y_340_ = v___y_366_;
v___y_341_ = v___y_367_;
v___y_342_ = v___x_374_;
v___y_343_ = v___y_370_;
v___y_344_ = v___x_375_;
goto v___jp_337_;
}
v___jp_376_:
{
switch(lean_obj_tag(v_port_383_))
{
case 0:
{
lean_object* v___x_387_; 
v___x_387_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__3));
v___y_362_ = v___y_377_;
v___y_363_ = v___y_378_;
v___y_364_ = v___y_379_;
v___y_365_ = v___y_386_;
v___y_366_ = v___y_380_;
v___y_367_ = v___y_382_;
v___y_368_ = v___y_381_;
v___y_369_ = v___y_384_;
v___y_370_ = v___y_385_;
v___y_371_ = v___x_387_;
goto v___jp_361_;
}
case 1:
{
lean_object* v___x_388_; 
v___x_388_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___y_362_ = v___y_377_;
v___y_363_ = v___y_378_;
v___y_364_ = v___y_379_;
v___y_365_ = v___y_386_;
v___y_366_ = v___y_380_;
v___y_367_ = v___y_382_;
v___y_368_ = v___y_381_;
v___y_369_ = v___y_384_;
v___y_370_ = v___y_385_;
v___y_371_ = v___x_388_;
goto v___jp_361_;
}
default: 
{
uint16_t v_port_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_port_389_ = lean_ctor_get_uint16(v_port_383_, 0);
lean_dec_ref_known(v_port_383_, 0);
v___x_390_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___x_391_ = lean_uint16_to_nat(v_port_389_);
v___x_392_ = l_Nat_reprFast(v___x_391_);
v___x_393_ = lean_string_append(v___x_390_, v___x_392_);
lean_dec_ref(v___x_392_);
v___y_362_ = v___y_377_;
v___y_363_ = v___y_378_;
v___y_364_ = v___y_379_;
v___y_365_ = v___y_386_;
v___y_366_ = v___y_380_;
v___y_367_ = v___y_382_;
v___y_368_ = v___y_381_;
v___y_369_ = v___y_384_;
v___y_370_ = v___y_385_;
v___y_371_ = v___x_393_;
goto v___jp_361_;
}
}
}
v___jp_394_:
{
switch(lean_obj_tag(v___y_396_))
{
case 0:
{
v___y_321_ = v___y_395_;
v___y_322_ = v___y_397_;
v___y_323_ = v___y_398_;
goto v___jp_320_;
}
case 1:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___x_400_ = lean_string_append(v___y_398_, v___x_399_);
v___y_321_ = v___y_395_;
v___y_322_ = v___y_397_;
v___y_323_ = v___x_400_;
goto v___jp_320_;
}
default: 
{
uint16_t v_port_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_port_401_ = lean_ctor_get_uint16(v___y_396_, 0);
lean_dec_ref_known(v___y_396_, 0);
v___x_402_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___x_403_ = lean_uint16_to_nat(v_port_401_);
v___x_404_ = l_Nat_reprFast(v___x_403_);
v___x_405_ = lean_string_append(v___x_402_, v___x_404_);
lean_dec_ref(v___x_404_);
v___x_406_ = lean_string_append(v___y_398_, v___x_405_);
lean_dec_ref(v___x_405_);
v___y_321_ = v___y_395_;
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
v___y_331_ = v_query_412_;
v___y_332_ = v___x_410_;
v___y_333_ = v___x_409_;
v___y_334_ = v_pathStr_414_;
goto v___jp_330_;
}
else
{
lean_object* v___x_418_; 
lean_dec_ref(v_pathStr_414_);
v___x_418_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__17));
v___y_331_ = v_query_412_;
v___y_332_ = v___x_410_;
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
v___y_354_ = v_query_423_;
v___y_355_ = v_scheme_421_;
v___y_356_ = v_path_422_;
v___y_357_ = v___x_410_;
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
lean_inc_ref(v_host_432_);
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
v___y_377_ = v_query_431_;
v___y_378_ = v_scheme_429_;
v___y_379_ = v___x_443_;
v___y_380_ = v_path_430_;
v___y_381_ = v___x_441_;
v___y_382_ = v___x_410_;
v_port_383_ = v_port_433_;
v___y_384_ = v___x_442_;
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
v___y_377_ = v_query_431_;
v___y_378_ = v_scheme_429_;
v___y_379_ = v___x_443_;
v___y_380_ = v_path_430_;
v___y_381_ = v___x_441_;
v___y_382_ = v___x_410_;
v_port_383_ = v_port_433_;
v___y_384_ = v___x_442_;
v___y_385_ = v___x_409_;
v___y_386_ = v___x_446_;
goto v___jp_376_;
}
default: 
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
v___y_377_ = v_query_431_;
v___y_378_ = v_scheme_429_;
v___y_379_ = v___x_443_;
v___y_380_ = v_path_430_;
v___y_381_ = v___x_441_;
v___y_382_ = v___x_410_;
v_port_383_ = v_port_433_;
v___y_384_ = v___x_442_;
v___y_385_ = v___x_409_;
v___y_386_ = v___x_452_;
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
lean_inc_ref(v_host_459_);
switch(lean_obj_tag(v_host_459_))
{
case 0:
{
lean_object* v_port_460_; lean_object* v_name_461_; 
v_port_460_ = lean_ctor_get(v_authority_458_, 2);
lean_inc(v_port_460_);
lean_dec_ref(v_authority_458_);
v_name_461_ = lean_ctor_get(v_host_459_, 0);
lean_inc_ref(v_name_461_);
lean_dec_ref_known(v_host_459_, 1);
v___y_395_ = v___x_410_;
v___y_396_ = v_port_460_;
v___y_397_ = v___x_409_;
v___y_398_ = v_name_461_;
goto v___jp_394_;
}
case 1:
{
lean_object* v_port_462_; lean_object* v_ipv4_463_; lean_object* v___x_464_; 
v_port_462_ = lean_ctor_get(v_authority_458_, 2);
lean_inc(v_port_462_);
lean_dec_ref(v_authority_458_);
v_ipv4_463_ = lean_ctor_get(v_host_459_, 0);
lean_inc_ref(v_ipv4_463_);
lean_dec_ref_known(v_host_459_, 1);
v___x_464_ = lean_uv_ntop_v4(v_ipv4_463_);
lean_dec_ref(v_ipv4_463_);
v___y_395_ = v___x_410_;
v___y_396_ = v_port_462_;
v___y_397_ = v___x_409_;
v___y_398_ = v___x_464_;
goto v___jp_394_;
}
default: 
{
lean_object* v_port_465_; lean_object* v_ipv6_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
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
v___y_395_ = v___x_410_;
v___y_396_ = v_port_465_;
v___y_397_ = v___x_409_;
v___y_398_ = v___x_471_;
goto v___jp_394_;
}
}
}
default: 
{
lean_object* v___x_472_; 
v___x_472_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__21));
v___y_321_ = v___x_410_;
v___y_322_ = v___x_409_;
v___y_323_ = v___x_472_;
goto v___jp_320_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__0));
v___x_518_ = lean_string_to_utf8(v___x_517_);
return v___x_518_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0);
v___x_520_ = lean_byte_array_size(v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__11));
v___x_523_ = lean_string_to_utf8(v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3);
v___x_525_ = lean_byte_array_size(v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__5(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__12));
v___x_527_ = lean_string_to_utf8(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__6(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__5, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__5_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__5);
v___x_529_ = lean_byte_array_size(v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__7(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__13));
v___x_531_ = lean_string_to_utf8(v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__8(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__7, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__7_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__7);
v___x_533_ = lean_byte_array_size(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__9(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__14));
v___x_535_ = lean_string_to_utf8(v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__10(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__9, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__9_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__9);
v___x_537_ = lean_byte_array_size(v___x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0(lean_object* v_out_538_, lean_object* v_req_539_){
_start:
{
uint8_t v_method_540_; uint8_t v_version_541_; lean_object* v_uri_542_; lean_object* v_headers_543_; lean_object* v___y_545_; lean_object* v___y_557_; lean_object* v___y_558_; uint8_t v___y_559_; lean_object* v___y_560_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; uint8_t v___y_595_; lean_object* v___y_596_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; uint8_t v___y_612_; uint8_t v___y_613_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; uint8_t v___y_632_; lean_object* v___y_633_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v_port_645_; lean_object* v___y_646_; lean_object* v___y_647_; uint8_t v___y_648_; lean_object* v___y_649_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; uint8_t v___y_661_; lean_object* v___y_662_; lean_object* v___y_666_; 
v_method_540_ = lean_ctor_get_uint8(v_req_539_, sizeof(void*)*2);
v_version_541_ = lean_ctor_get_uint8(v_req_539_, sizeof(void*)*2 + 1);
v_uri_542_ = lean_ctor_get(v_req_539_, 0);
lean_inc(v_uri_542_);
v_headers_543_ = lean_ctor_get(v_req_539_, 1);
lean_inc_ref(v_headers_543_);
lean_dec_ref(v_req_539_);
switch(v_method_540_)
{
case 0:
{
lean_object* v___x_736_; 
v___x_736_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__22));
v___y_666_ = v___x_736_;
goto v___jp_665_;
}
case 1:
{
lean_object* v___x_737_; 
v___x_737_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__23));
v___y_666_ = v___x_737_;
goto v___jp_665_;
}
case 2:
{
lean_object* v___x_738_; 
v___x_738_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__24));
v___y_666_ = v___x_738_;
goto v___jp_665_;
}
case 3:
{
lean_object* v___x_739_; 
v___x_739_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__25));
v___y_666_ = v___x_739_;
goto v___jp_665_;
}
case 4:
{
lean_object* v___x_740_; 
v___x_740_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__26));
v___y_666_ = v___x_740_;
goto v___jp_665_;
}
case 5:
{
lean_object* v___x_741_; 
v___x_741_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__27));
v___y_666_ = v___x_741_;
goto v___jp_665_;
}
case 6:
{
lean_object* v___x_742_; 
v___x_742_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__28));
v___y_666_ = v___x_742_;
goto v___jp_665_;
}
case 7:
{
lean_object* v___x_743_; 
v___x_743_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__29));
v___y_666_ = v___x_743_;
goto v___jp_665_;
}
case 8:
{
lean_object* v___x_744_; 
v___x_744_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__30));
v___y_666_ = v___x_744_;
goto v___jp_665_;
}
case 9:
{
lean_object* v___x_745_; 
v___x_745_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__31));
v___y_666_ = v___x_745_;
goto v___jp_665_;
}
case 10:
{
lean_object* v___x_746_; 
v___x_746_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__32));
v___y_666_ = v___x_746_;
goto v___jp_665_;
}
case 11:
{
lean_object* v___x_747_; 
v___x_747_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__33));
v___y_666_ = v___x_747_;
goto v___jp_665_;
}
case 12:
{
lean_object* v___x_748_; 
v___x_748_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__34));
v___y_666_ = v___x_748_;
goto v___jp_665_;
}
case 13:
{
lean_object* v___x_749_; 
v___x_749_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__35));
v___y_666_ = v___x_749_;
goto v___jp_665_;
}
case 14:
{
lean_object* v___x_750_; 
v___x_750_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__36));
v___y_666_ = v___x_750_;
goto v___jp_665_;
}
case 15:
{
lean_object* v___x_751_; 
v___x_751_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__37));
v___y_666_ = v___x_751_;
goto v___jp_665_;
}
case 16:
{
lean_object* v___x_752_; 
v___x_752_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__38));
v___y_666_ = v___x_752_;
goto v___jp_665_;
}
case 17:
{
lean_object* v___x_753_; 
v___x_753_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__39));
v___y_666_ = v___x_753_;
goto v___jp_665_;
}
case 18:
{
lean_object* v___x_754_; 
v___x_754_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__40));
v___y_666_ = v___x_754_;
goto v___jp_665_;
}
case 19:
{
lean_object* v___x_755_; 
v___x_755_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__41));
v___y_666_ = v___x_755_;
goto v___jp_665_;
}
case 20:
{
lean_object* v___x_756_; 
v___x_756_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__42));
v___y_666_ = v___x_756_;
goto v___jp_665_;
}
case 21:
{
lean_object* v___x_757_; 
v___x_757_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__43));
v___y_666_ = v___x_757_;
goto v___jp_665_;
}
case 22:
{
lean_object* v___x_758_; 
v___x_758_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__44));
v___y_666_ = v___x_758_;
goto v___jp_665_;
}
case 23:
{
lean_object* v___x_759_; 
v___x_759_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__45));
v___y_666_ = v___x_759_;
goto v___jp_665_;
}
case 24:
{
lean_object* v___x_760_; 
v___x_760_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__46));
v___y_666_ = v___x_760_;
goto v___jp_665_;
}
case 25:
{
lean_object* v___x_761_; 
v___x_761_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__47));
v___y_666_ = v___x_761_;
goto v___jp_665_;
}
case 26:
{
lean_object* v___x_762_; 
v___x_762_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__48));
v___y_666_ = v___x_762_;
goto v___jp_665_;
}
case 27:
{
lean_object* v___x_763_; 
v___x_763_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__49));
v___y_666_ = v___x_763_;
goto v___jp_665_;
}
case 28:
{
lean_object* v___x_764_; 
v___x_764_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__50));
v___y_666_ = v___x_764_;
goto v___jp_665_;
}
case 29:
{
lean_object* v___x_765_; 
v___x_765_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__51));
v___y_666_ = v___x_765_;
goto v___jp_665_;
}
case 30:
{
lean_object* v___x_766_; 
v___x_766_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__52));
v___y_666_ = v___x_766_;
goto v___jp_665_;
}
case 31:
{
lean_object* v___x_767_; 
v___x_767_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__53));
v___y_666_ = v___x_767_;
goto v___jp_665_;
}
case 32:
{
lean_object* v___x_768_; 
v___x_768_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__54));
v___y_666_ = v___x_768_;
goto v___jp_665_;
}
case 33:
{
lean_object* v___x_769_; 
v___x_769_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__55));
v___y_666_ = v___x_769_;
goto v___jp_665_;
}
case 34:
{
lean_object* v___x_770_; 
v___x_770_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__56));
v___y_666_ = v___x_770_;
goto v___jp_665_;
}
case 35:
{
lean_object* v___x_771_; 
v___x_771_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__57));
v___y_666_ = v___x_771_;
goto v___jp_665_;
}
case 36:
{
lean_object* v___x_772_; 
v___x_772_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__58));
v___y_666_ = v___x_772_;
goto v___jp_665_;
}
case 37:
{
lean_object* v___x_773_; 
v___x_773_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__59));
v___y_666_ = v___x_773_;
goto v___jp_665_;
}
case 38:
{
lean_object* v___x_774_; 
v___x_774_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__60));
v___y_666_ = v___x_774_;
goto v___jp_665_;
}
default: 
{
lean_object* v___x_775_; 
v___x_775_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__61));
v___y_666_ = v___x_775_;
goto v___jp_665_;
}
}
v___jp_544_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_546_ = lean_byte_array_size(v___y_545_);
v___x_547_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1);
v___x_550_ = 0;
v___x_551_ = lean_byte_array_copy_slice(v___x_547_, v___x_548_, v___y_545_, v___x_546_, v___x_549_, v___x_550_);
v___x_552_ = ((lean_object*)(l_Std_Http_Request_instEncodeV11Head___lam__0___closed__2));
v___x_553_ = l_Std_Http_Headers_fold___redArg(v_headers_543_, v___x_551_, v___x_552_);
lean_dec_ref(v_headers_543_);
v___x_554_ = lean_byte_array_size(v___x_553_);
v___x_555_ = lean_byte_array_copy_slice(v___x_547_, v___x_548_, v___x_553_, v___x_554_, v___x_549_, v___x_550_);
return v___x_555_;
}
v___jp_556_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; lean_object* v___x_566_; 
v___x_561_ = lean_byte_array_size(v___y_557_);
v___x_562_ = lean_string_to_utf8(v___y_560_);
v___x_563_ = lean_byte_array_size(v___x_562_);
v___x_564_ = lean_byte_array_copy_slice(v___x_562_, v___y_558_, v___y_557_, v___x_561_, v___x_563_, v___y_559_);
lean_dec_ref(v___x_562_);
v___x_565_ = 32;
v___x_566_ = lean_byte_array_push(v___x_564_, v___x_565_);
switch(v_version_541_)
{
case 0:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; lean_object* v___x_572_; 
v___x_567_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3);
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_byte_array_size(v___x_566_);
v___x_570_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4);
v___x_571_ = 0;
v___x_572_ = lean_byte_array_copy_slice(v___x_567_, v___x_568_, v___x_566_, v___x_569_, v___x_570_, v___x_571_);
v___y_545_ = v___x_572_;
goto v___jp_544_;
}
case 1:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; lean_object* v___x_578_; 
v___x_573_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__5, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__5_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__5);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_byte_array_size(v___x_566_);
v___x_576_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__6, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__6_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__6);
v___x_577_ = 0;
v___x_578_ = lean_byte_array_copy_slice(v___x_573_, v___x_574_, v___x_566_, v___x_575_, v___x_576_, v___x_577_);
v___y_545_ = v___x_578_;
goto v___jp_544_;
}
case 2:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; lean_object* v___x_584_; 
v___x_579_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__7, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__7_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__7);
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = lean_byte_array_size(v___x_566_);
v___x_582_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__8, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__8_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__8);
v___x_583_ = 0;
v___x_584_ = lean_byte_array_copy_slice(v___x_579_, v___x_580_, v___x_566_, v___x_581_, v___x_582_, v___x_583_);
v___y_545_ = v___x_584_;
goto v___jp_544_;
}
default: 
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; 
v___x_585_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__9, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__9_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__9);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_byte_array_size(v___x_566_);
v___x_588_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__10, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__10_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__10);
v___x_589_ = 0;
v___x_590_ = lean_byte_array_copy_slice(v___x_585_, v___x_586_, v___x_566_, v___x_587_, v___x_588_, v___x_589_);
v___y_545_ = v___x_590_;
goto v___jp_544_;
}
}
}
v___jp_591_:
{
switch(lean_obj_tag(v___y_593_))
{
case 0:
{
v___y_557_ = v___y_592_;
v___y_558_ = v___y_594_;
v___y_559_ = v___y_595_;
v___y_560_ = v___y_596_;
goto v___jp_556_;
}
case 1:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___x_598_ = lean_string_append(v___y_596_, v___x_597_);
v___y_557_ = v___y_592_;
v___y_558_ = v___y_594_;
v___y_559_ = v___y_595_;
v___y_560_ = v___x_598_;
goto v___jp_556_;
}
default: 
{
uint16_t v_port_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_port_599_ = lean_ctor_get_uint16(v___y_593_, 0);
lean_dec_ref_known(v___y_593_, 0);
v___x_600_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___x_601_ = lean_uint16_to_nat(v_port_599_);
v___x_602_ = l_Nat_reprFast(v___x_601_);
v___x_603_ = lean_string_append(v___x_600_, v___x_602_);
lean_dec_ref(v___x_602_);
v___x_604_ = lean_string_append(v___y_596_, v___x_603_);
lean_dec_ref(v___x_603_);
v___y_557_ = v___y_592_;
v___y_558_ = v___y_594_;
v___y_559_ = v___y_595_;
v___y_560_ = v___x_604_;
goto v___jp_556_;
}
}
}
v___jp_605_:
{
uint8_t v___x_614_; lean_object* v_pathPart_615_; lean_object* v_queryPart_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_614_ = 1;
v_pathPart_615_ = l_Std_Http_URI_Path_render(v___y_606_, v___y_613_, v___x_614_);
v_queryPart_616_ = l_Std_Http_URI_Query_formatOption(v___y_611_);
v___x_617_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___x_618_ = lean_string_append(v___y_608_, v___x_617_);
v___x_619_ = lean_string_append(v___x_618_, v___y_610_);
lean_dec_ref(v___y_610_);
v___x_620_ = lean_string_append(v___x_619_, v_pathPart_615_);
lean_dec_ref(v_pathPart_615_);
v___x_621_ = lean_string_append(v___x_620_, v_queryPart_616_);
lean_dec_ref(v_queryPart_616_);
v___y_557_ = v___y_607_;
v___y_558_ = v___y_609_;
v___y_559_ = v___y_612_;
v___y_560_ = v___x_621_;
goto v___jp_556_;
}
v___jp_622_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
lean_dec(v___y_627_);
lean_inc_ref(v___y_630_);
v___x_634_ = lean_string_append(v___y_630_, v___y_628_);
lean_dec_ref(v___y_628_);
v___x_635_ = lean_string_append(v___x_634_, v___y_633_);
lean_dec_ref(v___y_633_);
lean_inc_ref(v___y_624_);
v___x_636_ = lean_string_append(v___y_624_, v___x_635_);
lean_dec_ref(v___x_635_);
v___x_637_ = 1;
v___y_606_ = v___y_623_;
v___y_607_ = v___y_625_;
v___y_608_ = v___y_626_;
v___y_609_ = v___y_629_;
v___y_610_ = v___x_636_;
v___y_611_ = v___y_631_;
v___y_612_ = v___y_632_;
v___y_613_ = v___x_637_;
goto v___jp_605_;
}
v___jp_638_:
{
switch(lean_obj_tag(v_port_645_))
{
case 0:
{
lean_object* v___x_650_; 
v___x_650_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__3));
v___y_623_ = v___y_640_;
v___y_624_ = v___y_639_;
v___y_625_ = v___y_642_;
v___y_626_ = v___y_641_;
v___y_627_ = v___y_643_;
v___y_628_ = v___y_649_;
v___y_629_ = v___y_644_;
v___y_630_ = v___y_646_;
v___y_631_ = v___y_647_;
v___y_632_ = v___y_648_;
v___y_633_ = v___x_650_;
goto v___jp_622_;
}
case 1:
{
lean_object* v___x_651_; 
v___x_651_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___y_623_ = v___y_640_;
v___y_624_ = v___y_639_;
v___y_625_ = v___y_642_;
v___y_626_ = v___y_641_;
v___y_627_ = v___y_643_;
v___y_628_ = v___y_649_;
v___y_629_ = v___y_644_;
v___y_630_ = v___y_646_;
v___y_631_ = v___y_647_;
v___y_632_ = v___y_648_;
v___y_633_ = v___x_651_;
goto v___jp_622_;
}
default: 
{
uint16_t v_port_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_port_652_ = lean_ctor_get_uint16(v_port_645_, 0);
lean_dec_ref_known(v_port_645_, 0);
v___x_653_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___x_654_ = lean_uint16_to_nat(v_port_652_);
v___x_655_ = l_Nat_reprFast(v___x_654_);
v___x_656_ = lean_string_append(v___x_653_, v___x_655_);
lean_dec_ref(v___x_655_);
v___y_623_ = v___y_640_;
v___y_624_ = v___y_639_;
v___y_625_ = v___y_642_;
v___y_626_ = v___y_641_;
v___y_627_ = v___y_643_;
v___y_628_ = v___y_649_;
v___y_629_ = v___y_644_;
v___y_630_ = v___y_646_;
v___y_631_ = v___y_647_;
v___y_632_ = v___y_648_;
v___y_633_ = v___x_656_;
goto v___jp_622_;
}
}
}
v___jp_657_:
{
lean_object* v_queryStr_663_; lean_object* v___x_664_; 
v_queryStr_663_ = l_Std_Http_URI_Query_formatOption(v___y_659_);
v___x_664_ = lean_string_append(v___y_662_, v_queryStr_663_);
lean_dec_ref(v_queryStr_663_);
v___y_557_ = v___y_658_;
v___y_558_ = v___y_660_;
v___y_559_ = v___y_661_;
v___y_560_ = v___x_664_;
goto v___jp_556_;
}
v___jp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; lean_object* v___x_674_; 
v___x_667_ = lean_byte_array_size(v_out_538_);
lean_inc_ref(v___y_666_);
v___x_668_ = lean_string_to_utf8(v___y_666_);
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = lean_byte_array_size(v___x_668_);
v___x_671_ = 0;
v___x_672_ = lean_byte_array_copy_slice(v___x_668_, v___x_669_, v_out_538_, v___x_667_, v___x_670_, v___x_671_);
lean_dec_ref(v___x_668_);
v___x_673_ = 32;
v___x_674_ = lean_byte_array_push(v___x_672_, v___x_673_);
switch(lean_obj_tag(v_uri_542_))
{
case 0:
{
lean_object* v_path_675_; lean_object* v_query_676_; uint8_t v___x_677_; lean_object* v_pathStr_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v_path_675_ = lean_ctor_get(v_uri_542_, 0);
lean_inc_ref(v_path_675_);
v_query_676_ = lean_ctor_get(v_uri_542_, 1);
lean_inc(v_query_676_);
lean_dec_ref_known(v_uri_542_, 2);
v___x_677_ = 1;
v_pathStr_678_ = l_Std_Http_URI_Path_render(v_path_675_, v___x_677_, v___x_677_);
v___x_679_ = lean_string_utf8_byte_size(v_pathStr_678_);
v___x_680_ = lean_nat_dec_eq(v___x_679_, v___x_669_);
if (v___x_680_ == 0)
{
v___y_658_ = v___x_674_;
v___y_659_ = v_query_676_;
v___y_660_ = v___x_669_;
v___y_661_ = v___x_671_;
v___y_662_ = v_pathStr_678_;
goto v___jp_657_;
}
else
{
lean_object* v___x_681_; 
lean_dec_ref(v_pathStr_678_);
v___x_681_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__17));
v___y_658_ = v___x_674_;
v___y_659_ = v_query_676_;
v___y_660_ = v___x_669_;
v___y_661_ = v___x_671_;
v___y_662_ = v___x_681_;
goto v___jp_657_;
}
}
case 1:
{
lean_object* v_uri_682_; lean_object* v_authority_683_; 
v_uri_682_ = lean_ctor_get(v_uri_542_, 0);
lean_inc_ref(v_uri_682_);
lean_dec_ref_known(v_uri_542_, 1);
v_authority_683_ = lean_ctor_get(v_uri_682_, 1);
lean_inc(v_authority_683_);
if (lean_obj_tag(v_authority_683_) == 0)
{
lean_object* v_scheme_684_; lean_object* v_path_685_; lean_object* v_query_686_; lean_object* v___x_687_; 
v_scheme_684_ = lean_ctor_get(v_uri_682_, 0);
lean_inc_ref(v_scheme_684_);
v_path_685_ = lean_ctor_get(v_uri_682_, 2);
lean_inc_ref(v_path_685_);
v_query_686_ = lean_ctor_get(v_uri_682_, 3);
lean_inc(v_query_686_);
lean_dec_ref(v_uri_682_);
v___x_687_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__3));
v___y_606_ = v_path_685_;
v___y_607_ = v___x_674_;
v___y_608_ = v_scheme_684_;
v___y_609_ = v___x_669_;
v___y_610_ = v___x_687_;
v___y_611_ = v_query_686_;
v___y_612_ = v___x_671_;
v___y_613_ = v___x_671_;
goto v___jp_605_;
}
else
{
lean_object* v_val_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_720_; 
v_val_688_ = lean_ctor_get(v_authority_683_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v_authority_683_);
if (v_isSharedCheck_720_ == 0)
{
v___x_690_ = v_authority_683_;
v_isShared_691_ = v_isSharedCheck_720_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_val_688_);
lean_dec(v_authority_683_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_720_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_scheme_692_; lean_object* v_path_693_; lean_object* v_query_694_; lean_object* v_host_695_; lean_object* v_port_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_718_; 
v_scheme_692_ = lean_ctor_get(v_uri_682_, 0);
lean_inc_ref(v_scheme_692_);
v_path_693_ = lean_ctor_get(v_uri_682_, 2);
lean_inc_ref(v_path_693_);
v_query_694_ = lean_ctor_get(v_uri_682_, 3);
lean_inc(v_query_694_);
lean_dec_ref(v_uri_682_);
v_host_695_ = lean_ctor_get(v_val_688_, 1);
v_port_696_ = lean_ctor_get(v_val_688_, 2);
v_isSharedCheck_718_ = !lean_is_exclusive(v_val_688_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v_val_688_, 0);
lean_dec(v_unused_719_);
v___x_698_ = v_val_688_;
v_isShared_699_ = v_isSharedCheck_718_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_port_696_);
lean_inc(v_host_695_);
lean_dec(v_val_688_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_718_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_700_ = lean_box(0);
lean_inc(v_port_696_);
lean_inc_ref(v_host_695_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_host_695_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_port_696_);
v___x_702_ = v_reuseFailAlloc_717_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_702_);
v___x_704_ = v___x_690_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_716_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__18));
v___x_706_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__3));
switch(lean_obj_tag(v_host_695_))
{
case 0:
{
lean_object* v_name_707_; 
v_name_707_ = lean_ctor_get(v_host_695_, 0);
lean_inc_ref(v_name_707_);
lean_dec_ref_known(v_host_695_, 1);
v___y_639_ = v___x_705_;
v___y_640_ = v_path_693_;
v___y_641_ = v_scheme_692_;
v___y_642_ = v___x_674_;
v___y_643_ = v___x_704_;
v___y_644_ = v___x_669_;
v_port_645_ = v_port_696_;
v___y_646_ = v___x_706_;
v___y_647_ = v_query_694_;
v___y_648_ = v___x_671_;
v___y_649_ = v_name_707_;
goto v___jp_638_;
}
case 1:
{
lean_object* v_ipv4_708_; lean_object* v___x_709_; 
v_ipv4_708_ = lean_ctor_get(v_host_695_, 0);
lean_inc_ref(v_ipv4_708_);
lean_dec_ref_known(v_host_695_, 1);
v___x_709_ = lean_uv_ntop_v4(v_ipv4_708_);
lean_dec_ref(v_ipv4_708_);
v___y_639_ = v___x_705_;
v___y_640_ = v_path_693_;
v___y_641_ = v_scheme_692_;
v___y_642_ = v___x_674_;
v___y_643_ = v___x_704_;
v___y_644_ = v___x_669_;
v_port_645_ = v_port_696_;
v___y_646_ = v___x_706_;
v___y_647_ = v_query_694_;
v___y_648_ = v___x_671_;
v___y_649_ = v___x_709_;
goto v___jp_638_;
}
default: 
{
lean_object* v_ipv6_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v_ipv6_710_ = lean_ctor_get(v_host_695_, 0);
lean_inc_ref(v_ipv6_710_);
lean_dec_ref_known(v_host_695_, 1);
v___x_711_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__19));
v___x_712_ = lean_uv_ntop_v6(v_ipv6_710_);
lean_dec_ref(v_ipv6_710_);
v___x_713_ = lean_string_append(v___x_711_, v___x_712_);
lean_dec_ref(v___x_712_);
v___x_714_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__20));
v___x_715_ = lean_string_append(v___x_713_, v___x_714_);
v___y_639_ = v___x_705_;
v___y_640_ = v_path_693_;
v___y_641_ = v_scheme_692_;
v___y_642_ = v___x_674_;
v___y_643_ = v___x_704_;
v___y_644_ = v___x_669_;
v_port_645_ = v_port_696_;
v___y_646_ = v___x_706_;
v___y_647_ = v_query_694_;
v___y_648_ = v___x_671_;
v___y_649_ = v___x_715_;
goto v___jp_638_;
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
lean_object* v_authority_721_; lean_object* v_host_722_; 
v_authority_721_ = lean_ctor_get(v_uri_542_, 0);
lean_inc_ref(v_authority_721_);
lean_dec_ref_known(v_uri_542_, 1);
v_host_722_ = lean_ctor_get(v_authority_721_, 1);
lean_inc_ref(v_host_722_);
switch(lean_obj_tag(v_host_722_))
{
case 0:
{
lean_object* v_port_723_; lean_object* v_name_724_; 
v_port_723_ = lean_ctor_get(v_authority_721_, 2);
lean_inc(v_port_723_);
lean_dec_ref(v_authority_721_);
v_name_724_ = lean_ctor_get(v_host_722_, 0);
lean_inc_ref(v_name_724_);
lean_dec_ref_known(v_host_722_, 1);
v___y_592_ = v___x_674_;
v___y_593_ = v_port_723_;
v___y_594_ = v___x_669_;
v___y_595_ = v___x_671_;
v___y_596_ = v_name_724_;
goto v___jp_591_;
}
case 1:
{
lean_object* v_port_725_; lean_object* v_ipv4_726_; lean_object* v___x_727_; 
v_port_725_ = lean_ctor_get(v_authority_721_, 2);
lean_inc(v_port_725_);
lean_dec_ref(v_authority_721_);
v_ipv4_726_ = lean_ctor_get(v_host_722_, 0);
lean_inc_ref(v_ipv4_726_);
lean_dec_ref_known(v_host_722_, 1);
v___x_727_ = lean_uv_ntop_v4(v_ipv4_726_);
lean_dec_ref(v_ipv4_726_);
v___y_592_ = v___x_674_;
v___y_593_ = v_port_725_;
v___y_594_ = v___x_669_;
v___y_595_ = v___x_671_;
v___y_596_ = v___x_727_;
goto v___jp_591_;
}
default: 
{
lean_object* v_port_728_; lean_object* v_ipv6_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_port_728_ = lean_ctor_get(v_authority_721_, 2);
lean_inc(v_port_728_);
lean_dec_ref(v_authority_721_);
v_ipv6_729_ = lean_ctor_get(v_host_722_, 0);
lean_inc_ref(v_ipv6_729_);
lean_dec_ref_known(v_host_722_, 1);
v___x_730_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__19));
v___x_731_ = lean_uv_ntop_v6(v_ipv6_729_);
lean_dec_ref(v_ipv6_729_);
v___x_732_ = lean_string_append(v___x_730_, v___x_731_);
lean_dec_ref(v___x_731_);
v___x_733_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__20));
v___x_734_ = lean_string_append(v___x_732_, v___x_733_);
v___y_592_ = v___x_674_;
v___y_593_ = v_port_728_;
v___y_594_ = v___x_669_;
v___y_595_ = v___x_671_;
v___y_596_ = v___x_734_;
goto v___jp_591_;
}
}
}
default: 
{
lean_object* v___x_735_; 
v___x_735_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__21));
v___y_557_ = v___x_674_;
v___y_558_ = v___x_669_;
v___y_559_ = v___x_671_;
v___y_560_ = v___x_735_;
goto v___jp_556_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__0(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; uint8_t v___x_781_; lean_object* v___x_782_; 
v___x_778_ = l_Std_Http_Headers_empty;
v___x_779_ = lean_box(3);
v___x_780_ = 1;
v___x_781_ = 8;
v___x_782_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_782_, 0, v___x_779_);
lean_ctor_set(v___x_782_, 1, v___x_778_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*2, v___x_781_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*2 + 1, v___x_780_);
return v___x_782_;
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__1(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_783_ = l_Std_Http_Extensions_empty;
v___x_784_ = lean_obj_once(&l_Std_Http_Request_new___closed__0, &l_Std_Http_Request_new___closed__0_once, _init_l_Std_Http_Request_new___closed__0);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v___x_783_);
return v___x_785_;
}
}
static lean_object* _init_l_Std_Http_Request_new(void){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = lean_obj_once(&l_Std_Http_Request_new___closed__1, &l_Std_Http_Request_new___closed__1_once, _init_l_Std_Http_Request_new___closed__1);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method(lean_object* v_builder_787_, uint8_t v_method_788_){
_start:
{
lean_object* v_line_789_; lean_object* v_extensions_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_807_; 
v_line_789_ = lean_ctor_get(v_builder_787_, 0);
v_extensions_790_ = lean_ctor_get(v_builder_787_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_builder_787_);
if (v_isSharedCheck_807_ == 0)
{
v___x_792_ = v_builder_787_;
v_isShared_793_ = v_isSharedCheck_807_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_extensions_790_);
lean_inc(v_line_789_);
lean_dec(v_builder_787_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_807_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
uint8_t v_version_794_; lean_object* v_uri_795_; lean_object* v_headers_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_806_; 
v_version_794_ = lean_ctor_get_uint8(v_line_789_, sizeof(void*)*2 + 1);
v_uri_795_ = lean_ctor_get(v_line_789_, 0);
v_headers_796_ = lean_ctor_get(v_line_789_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v_line_789_);
if (v_isSharedCheck_806_ == 0)
{
v___x_798_ = v_line_789_;
v_isShared_799_ = v_isSharedCheck_806_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_headers_796_);
lean_inc(v_uri_795_);
lean_dec(v_line_789_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_806_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_uri_795_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_headers_796_);
lean_ctor_set_uint8(v_reuseFailAlloc_805_, sizeof(void*)*2 + 1, v_version_794_);
v___x_801_ = v_reuseFailAlloc_805_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_803_; 
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*2, v_method_788_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_801_);
v___x_803_ = v___x_792_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_extensions_790_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method___boxed(lean_object* v_builder_808_, lean_object* v_method_809_){
_start:
{
uint8_t v_method_boxed_810_; lean_object* v_res_811_; 
v_method_boxed_810_ = lean_unbox(v_method_809_);
v_res_811_ = l_Std_Http_Request_Builder_method(v_builder_808_, v_method_boxed_810_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version(lean_object* v_builder_812_, uint8_t v_version_813_){
_start:
{
lean_object* v_line_814_; lean_object* v_extensions_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_832_; 
v_line_814_ = lean_ctor_get(v_builder_812_, 0);
v_extensions_815_ = lean_ctor_get(v_builder_812_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v_builder_812_);
if (v_isSharedCheck_832_ == 0)
{
v___x_817_ = v_builder_812_;
v_isShared_818_ = v_isSharedCheck_832_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_extensions_815_);
lean_inc(v_line_814_);
lean_dec(v_builder_812_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_832_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
uint8_t v_method_819_; lean_object* v_uri_820_; lean_object* v_headers_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_831_; 
v_method_819_ = lean_ctor_get_uint8(v_line_814_, sizeof(void*)*2);
v_uri_820_ = lean_ctor_get(v_line_814_, 0);
v_headers_821_ = lean_ctor_get(v_line_814_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_line_814_);
if (v_isSharedCheck_831_ == 0)
{
v___x_823_ = v_line_814_;
v_isShared_824_ = v_isSharedCheck_831_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_headers_821_);
lean_inc(v_uri_820_);
lean_dec(v_line_814_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_831_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_uri_820_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_headers_821_);
lean_ctor_set_uint8(v_reuseFailAlloc_830_, sizeof(void*)*2, v_method_819_);
v___x_826_ = v_reuseFailAlloc_830_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_828_; 
lean_ctor_set_uint8(v___x_826_, sizeof(void*)*2 + 1, v_version_813_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_826_);
v___x_828_ = v___x_817_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_extensions_815_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version___boxed(lean_object* v_builder_833_, lean_object* v_version_834_){
_start:
{
uint8_t v_version_boxed_835_; lean_object* v_res_836_; 
v_version_boxed_835_ = lean_unbox(v_version_834_);
v_res_836_ = l_Std_Http_Request_Builder_version(v_builder_833_, v_version_boxed_835_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri(lean_object* v_builder_837_, lean_object* v_uri_838_){
_start:
{
lean_object* v_line_839_; lean_object* v_extensions_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_858_; 
v_line_839_ = lean_ctor_get(v_builder_837_, 0);
v_extensions_840_ = lean_ctor_get(v_builder_837_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v_builder_837_);
if (v_isSharedCheck_858_ == 0)
{
v___x_842_ = v_builder_837_;
v_isShared_843_ = v_isSharedCheck_858_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_extensions_840_);
lean_inc(v_line_839_);
lean_dec(v_builder_837_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_858_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
uint8_t v_method_844_; uint8_t v_version_845_; lean_object* v_headers_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_856_; 
v_method_844_ = lean_ctor_get_uint8(v_line_839_, sizeof(void*)*2);
v_version_845_ = lean_ctor_get_uint8(v_line_839_, sizeof(void*)*2 + 1);
v_headers_846_ = lean_ctor_get(v_line_839_, 1);
v_isSharedCheck_856_ = !lean_is_exclusive(v_line_839_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; 
v_unused_857_ = lean_ctor_get(v_line_839_, 0);
lean_dec(v_unused_857_);
v___x_848_ = v_line_839_;
v_isShared_849_ = v_isSharedCheck_856_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_headers_846_);
lean_dec(v_line_839_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_856_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v_uri_838_);
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_uri_838_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_headers_846_);
lean_ctor_set_uint8(v_reuseFailAlloc_855_, sizeof(void*)*2, v_method_844_);
lean_ctor_set_uint8(v_reuseFailAlloc_855_, sizeof(void*)*2 + 1, v_version_845_);
v___x_851_ = v_reuseFailAlloc_855_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_853_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_851_);
v___x_853_ = v___x_842_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_extensions_840_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(lean_object* v_msg_859_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = l_Std_Http_instInhabitedRequestTarget_default;
v___x_861_ = lean_panic_fn_borrowed(v___x_860_, v_msg_859_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___lam__0(lean_object* v___x_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_865_, v___y_866_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_pos_868_; lean_object* v_array_869_; lean_object* v_idx_870_; lean_object* v___x_871_; uint8_t v___x_872_; 
v_pos_868_ = lean_ctor_get(v___x_867_, 0);
v_array_869_ = lean_ctor_get(v_pos_868_, 0);
v_idx_870_ = lean_ctor_get(v_pos_868_, 1);
v___x_871_ = lean_byte_array_size(v_array_869_);
v___x_872_ = lean_nat_dec_lt(v_idx_870_, v___x_871_);
if (v___x_872_ == 0)
{
return v___x_867_;
}
else
{
lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_880_; 
lean_inc(v_pos_868_);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; lean_object* v_unused_882_; 
v_unused_881_ = lean_ctor_get(v___x_867_, 1);
lean_dec(v_unused_881_);
v_unused_882_ = lean_ctor_get(v___x_867_, 0);
lean_dec(v_unused_882_);
v___x_874_ = v___x_867_;
v_isShared_875_ = v_isSharedCheck_880_;
goto v_resetjp_873_;
}
else
{
lean_dec(v___x_867_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_880_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_876_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___lam__0___closed__1));
if (v_isShared_875_ == 0)
{
lean_ctor_set_tag(v___x_874_, 1);
lean_ctor_set(v___x_874_, 1, v___x_876_);
v___x_878_ = v___x_874_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_pos_868_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
else
{
return v___x_867_;
}
}
}
static lean_object* _init_l_Std_Http_Request_Builder_uri_x21___closed__5(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_893_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__4));
v___x_894_ = lean_unsigned_to_nat(12u);
v___x_895_ = lean_unsigned_to_nat(45u);
v___x_896_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__3));
v___x_897_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__2));
v___x_898_ = l_mkPanicMessageWithDecl(v___x_897_, v___x_896_, v___x_895_, v___x_894_, v___x_893_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21(lean_object* v_builder_899_, lean_object* v_uri_900_){
_start:
{
lean_object* v___y_902_; lean_object* v___f_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___f_923_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__1));
v___x_924_ = lean_string_to_utf8(v_uri_900_);
v___x_925_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_923_, v___x_924_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec_ref_known(v___x_925_, 1);
v___x_926_ = lean_obj_once(&l_Std_Http_Request_Builder_uri_x21___closed__5, &l_Std_Http_Request_Builder_uri_x21___closed__5_once, _init_l_Std_Http_Request_Builder_uri_x21___closed__5);
v___x_927_ = l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(v___x_926_);
v___y_902_ = v___x_927_;
goto v___jp_901_;
}
else
{
lean_object* v_a_928_; 
v_a_928_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_925_, 1);
v___y_902_ = v_a_928_;
goto v___jp_901_;
}
v___jp_901_:
{
lean_object* v_line_903_; lean_object* v_extensions_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_922_; 
v_line_903_ = lean_ctor_get(v_builder_899_, 0);
v_extensions_904_ = lean_ctor_get(v_builder_899_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v_builder_899_);
if (v_isSharedCheck_922_ == 0)
{
v___x_906_ = v_builder_899_;
v_isShared_907_ = v_isSharedCheck_922_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_extensions_904_);
lean_inc(v_line_903_);
lean_dec(v_builder_899_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_922_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
uint8_t v_method_908_; uint8_t v_version_909_; lean_object* v_headers_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_920_; 
v_method_908_ = lean_ctor_get_uint8(v_line_903_, sizeof(void*)*2);
v_version_909_ = lean_ctor_get_uint8(v_line_903_, sizeof(void*)*2 + 1);
v_headers_910_ = lean_ctor_get(v_line_903_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_line_903_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v_line_903_, 0);
lean_dec(v_unused_921_);
v___x_912_ = v_line_903_;
v_isShared_913_ = v_isSharedCheck_920_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_headers_910_);
lean_dec(v_line_903_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_920_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___y_902_);
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___y_902_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_headers_910_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*2, v_method_908_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*2 + 1, v_version_909_);
v___x_915_ = v_reuseFailAlloc_919_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_917_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_915_);
v___x_917_ = v___x_906_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_extensions_904_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headers(lean_object* v_builder_929_, lean_object* v_headers_930_){
_start:
{
lean_object* v_line_931_; lean_object* v_extensions_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_950_; 
v_line_931_ = lean_ctor_get(v_builder_929_, 0);
v_extensions_932_ = lean_ctor_get(v_builder_929_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_builder_929_);
if (v_isSharedCheck_950_ == 0)
{
v___x_934_ = v_builder_929_;
v_isShared_935_ = v_isSharedCheck_950_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_extensions_932_);
lean_inc(v_line_931_);
lean_dec(v_builder_929_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_950_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
uint8_t v_method_936_; uint8_t v_version_937_; lean_object* v_uri_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_948_; 
v_method_936_ = lean_ctor_get_uint8(v_line_931_, sizeof(void*)*2);
v_version_937_ = lean_ctor_get_uint8(v_line_931_, sizeof(void*)*2 + 1);
v_uri_938_ = lean_ctor_get(v_line_931_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_line_931_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_line_931_, 1);
lean_dec(v_unused_949_);
v___x_940_ = v_line_931_;
v_isShared_941_ = v_isSharedCheck_948_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_uri_938_);
lean_dec(v_line_931_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_948_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v_headers_930_);
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_uri_938_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_headers_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*2, v_method_936_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*2 + 1, v_version_937_);
v___x_943_ = v_reuseFailAlloc_947_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_945_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_943_);
v___x_945_ = v___x_934_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_extensions_932_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header(lean_object* v_builder_951_, lean_object* v_key_952_, lean_object* v_value_953_){
_start:
{
lean_object* v_line_954_; lean_object* v_extensions_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_975_; 
v_line_954_ = lean_ctor_get(v_builder_951_, 0);
v_extensions_955_ = lean_ctor_get(v_builder_951_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_builder_951_);
if (v_isSharedCheck_975_ == 0)
{
v___x_957_ = v_builder_951_;
v_isShared_958_ = v_isSharedCheck_975_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_extensions_955_);
lean_inc(v_line_954_);
lean_dec(v_builder_951_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_975_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
uint8_t v_method_959_; uint8_t v_version_960_; lean_object* v_uri_961_; lean_object* v_headers_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_974_; 
v_method_959_ = lean_ctor_get_uint8(v_line_954_, sizeof(void*)*2);
v_version_960_ = lean_ctor_get_uint8(v_line_954_, sizeof(void*)*2 + 1);
v_uri_961_ = lean_ctor_get(v_line_954_, 0);
v_headers_962_ = lean_ctor_get(v_line_954_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v_line_954_);
if (v_isSharedCheck_974_ == 0)
{
v___x_964_ = v_line_954_;
v_isShared_965_ = v_isSharedCheck_974_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_headers_962_);
lean_inc(v_uri_961_);
lean_dec(v_line_954_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_974_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v_key_952_);
lean_ctor_set(v___x_966_, 1, v_value_953_);
v___x_967_ = lean_array_push(v_headers_962_, v___x_966_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v___x_967_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_uri_961_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v___x_967_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*2, v_method_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*2 + 1, v_version_960_);
v___x_969_ = v_reuseFailAlloc_973_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_971_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_969_);
v___x_971_ = v___x_957_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_extensions_955_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x21(lean_object* v_builder_976_, lean_object* v_key_977_, lean_object* v_value_978_){
_start:
{
lean_object* v_line_979_; lean_object* v_extensions_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1002_; 
v_line_979_ = lean_ctor_get(v_builder_976_, 0);
v_extensions_980_ = lean_ctor_get(v_builder_976_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_builder_976_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_982_ = v_builder_976_;
v_isShared_983_ = v_isSharedCheck_1002_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_extensions_980_);
lean_inc(v_line_979_);
lean_dec(v_builder_976_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1002_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
uint8_t v_method_984_; uint8_t v_version_985_; lean_object* v_uri_986_; lean_object* v_headers_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1001_; 
v_method_984_ = lean_ctor_get_uint8(v_line_979_, sizeof(void*)*2);
v_version_985_ = lean_ctor_get_uint8(v_line_979_, sizeof(void*)*2 + 1);
v_uri_986_ = lean_ctor_get(v_line_979_, 0);
v_headers_987_ = lean_ctor_get(v_line_979_, 1);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_line_979_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_989_ = v_line_979_;
v_isShared_990_ = v_isSharedCheck_1001_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_headers_987_);
lean_inc(v_uri_986_);
lean_dec(v_line_979_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1001_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v_key_991_; lean_object* v_value_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
v_key_991_ = l_Std_Http_Header_Name_ofString_x21(v_key_977_);
v_value_992_ = l_Std_Http_Header_Value_ofString_x21(v_value_978_);
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v_key_991_);
lean_ctor_set(v___x_993_, 1, v_value_992_);
v___x_994_ = lean_array_push(v_headers_987_, v___x_993_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 1, v___x_994_);
v___x_996_ = v___x_989_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_uri_986_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v___x_994_);
lean_ctor_set_uint8(v_reuseFailAlloc_1000_, sizeof(void*)*2, v_method_984_);
lean_ctor_set_uint8(v_reuseFailAlloc_1000_, sizeof(void*)*2 + 1, v_version_985_);
v___x_996_ = v_reuseFailAlloc_1000_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_998_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_996_);
v___x_998_ = v___x_982_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_extensions_980_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x3f(lean_object* v_builder_1003_, lean_object* v_key_1004_, lean_object* v_value_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Std_Http_Header_Name_ofString_x3f(v_key_1004_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v___x_1007_; 
lean_dec_ref(v_value_1005_);
lean_dec_ref(v_builder_1003_);
v___x_1007_ = lean_box(0);
return v___x_1007_;
}
else
{
lean_object* v_val_1008_; lean_object* v___x_1009_; 
v_val_1008_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_val_1008_);
lean_dec_ref_known(v___x_1006_, 1);
v___x_1009_ = l_Std_Http_Header_Value_ofString_x3f(v_value_1005_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v___x_1010_; 
lean_dec(v_val_1008_);
lean_dec_ref(v_builder_1003_);
v___x_1010_ = lean_box(0);
return v___x_1010_;
}
else
{
lean_object* v_line_1011_; lean_object* v_val_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1041_; 
v_line_1011_ = lean_ctor_get(v_builder_1003_, 0);
lean_inc_ref(v_line_1011_);
v_val_1012_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1014_ = v___x_1009_;
v_isShared_1015_ = v_isSharedCheck_1041_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_val_1012_);
lean_dec(v___x_1009_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1041_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v_extensions_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1039_; 
v_extensions_1016_ = lean_ctor_get(v_builder_1003_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_builder_1003_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; 
v_unused_1040_ = lean_ctor_get(v_builder_1003_, 0);
lean_dec(v_unused_1040_);
v___x_1018_ = v_builder_1003_;
v_isShared_1019_ = v_isSharedCheck_1039_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_extensions_1016_);
lean_dec(v_builder_1003_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1039_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
uint8_t v_method_1020_; uint8_t v_version_1021_; lean_object* v_uri_1022_; lean_object* v_headers_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1038_; 
v_method_1020_ = lean_ctor_get_uint8(v_line_1011_, sizeof(void*)*2);
v_version_1021_ = lean_ctor_get_uint8(v_line_1011_, sizeof(void*)*2 + 1);
v_uri_1022_ = lean_ctor_get(v_line_1011_, 0);
v_headers_1023_ = lean_ctor_get(v_line_1011_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_line_1011_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1025_ = v_line_1011_;
v_isShared_1026_ = v_isSharedCheck_1038_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_headers_1023_);
lean_inc(v_uri_1022_);
lean_dec(v_line_1011_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1038_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_val_1008_);
lean_ctor_set(v___x_1027_, 1, v_val_1012_);
v___x_1028_ = lean_array_push(v_headers_1023_, v___x_1027_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 1, v___x_1028_);
v___x_1030_ = v___x_1025_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_uri_1022_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v___x_1028_);
lean_ctor_set_uint8(v_reuseFailAlloc_1037_, sizeof(void*)*2, v_method_1020_);
lean_ctor_set_uint8(v_reuseFailAlloc_1037_, sizeof(void*)*2 + 1, v_version_1021_);
v___x_1030_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1030_);
v___x_1032_ = v___x_1018_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_extensions_1016_);
v___x_1032_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1034_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1032_);
v___x_1034_ = v___x_1014_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
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
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headerOpt(lean_object* v_builder_1042_, lean_object* v_key_1043_, lean_object* v_value_1044_){
_start:
{
if (lean_obj_tag(v_value_1044_) == 0)
{
lean_dec_ref(v_key_1043_);
return v_builder_1042_;
}
else
{
lean_object* v_val_1045_; lean_object* v___x_1046_; 
v_val_1045_ = lean_ctor_get(v_value_1044_, 0);
lean_inc(v_val_1045_);
lean_dec_ref_known(v_value_1044_, 1);
v___x_1046_ = l_Std_Http_Request_Builder_header(v_builder_1042_, v_key_1043_, v_val_1045_);
return v___x_1046_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension___redArg(lean_object* v_builder_1048_, lean_object* v_inst_1049_, lean_object* v_data_1050_){
_start:
{
lean_object* v_line_1051_; lean_object* v_extensions_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1063_; 
v_line_1051_ = lean_ctor_get(v_builder_1048_, 0);
v_extensions_1052_ = lean_ctor_get(v_builder_1048_, 1);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_builder_1048_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1054_ = v_builder_1048_;
v_isShared_1055_ = v_isSharedCheck_1063_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_extensions_1052_);
lean_inc(v_line_1051_);
lean_dec(v_builder_1048_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1063_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v_dyn_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v_dyn_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_1056_, 0, v_inst_1049_);
lean_ctor_set(v_dyn_1056_, 1, v_data_1050_);
v___x_1057_ = ((lean_object*)(l_Std_Http_Request_Builder_extension___redArg___closed__0));
v___x_1058_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_1056_);
v___x_1059_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1057_, v___x_1058_, v_dyn_1056_, v_extensions_1052_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v___x_1059_);
v___x_1061_ = v___x_1054_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_line_1051_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension(lean_object* v_00_u03b1_1064_, lean_object* v_builder_1065_, lean_object* v_inst_1066_, lean_object* v_data_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Std_Http_Request_Builder_extension___redArg(v_builder_1065_, v_inst_1066_, v_data_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object* v_builder_1069_, lean_object* v_body_1070_){
_start:
{
lean_object* v_line_1071_; lean_object* v_extensions_1072_; lean_object* v___x_1073_; 
v_line_1071_ = lean_ctor_get(v_builder_1069_, 0);
v_extensions_1072_ = lean_ctor_get(v_builder_1069_, 1);
lean_inc(v_extensions_1072_);
lean_inc_ref(v_line_1071_);
v___x_1073_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1073_, 0, v_line_1071_);
lean_ctor_set(v___x_1073_, 1, v_body_1070_);
lean_ctor_set(v___x_1073_, 2, v_extensions_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg___boxed(lean_object* v_builder_1074_, lean_object* v_body_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1074_, v_body_1075_);
lean_dec_ref(v_builder_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body(lean_object* v_t_1077_, lean_object* v_builder_1078_, lean_object* v_body_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1078_, v_body_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___boxed(lean_object* v_t_1081_, lean_object* v_builder_1082_, lean_object* v_body_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Std_Http_Request_Builder_body(v_t_1081_, v_builder_1082_, v_body_1083_);
lean_dec_ref(v_builder_1082_);
return v_res_1084_;
}
}
static lean_object* _init_l_Std_Http_Request_get___closed__0(void){
_start:
{
uint8_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = 8;
v___x_1086_ = l_Std_Http_Request_new;
v___x_1087_ = l_Std_Http_Request_Builder_method(v___x_1086_, v___x_1085_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_get(lean_object* v_uri_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_obj_once(&l_Std_Http_Request_get___closed__0, &l_Std_Http_Request_get___closed__0_once, _init_l_Std_Http_Request_get___closed__0);
v___x_1090_ = l_Std_Http_Request_Builder_uri(v___x_1089_, v_uri_1088_);
return v___x_1090_;
}
}
static lean_object* _init_l_Std_Http_Request_post___closed__0(void){
_start:
{
uint8_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = 23;
v___x_1092_ = l_Std_Http_Request_new;
v___x_1093_ = l_Std_Http_Request_Builder_method(v___x_1092_, v___x_1091_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_post(lean_object* v_uri_1094_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_obj_once(&l_Std_Http_Request_post___closed__0, &l_Std_Http_Request_post___closed__0_once, _init_l_Std_Http_Request_post___closed__0);
v___x_1096_ = l_Std_Http_Request_Builder_uri(v___x_1095_, v_uri_1094_);
return v___x_1096_;
}
}
static lean_object* _init_l_Std_Http_Request_put___closed__0(void){
_start:
{
uint8_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = 27;
v___x_1098_ = l_Std_Http_Request_new;
v___x_1099_ = l_Std_Http_Request_Builder_method(v___x_1098_, v___x_1097_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_put(lean_object* v_uri_1100_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_obj_once(&l_Std_Http_Request_put___closed__0, &l_Std_Http_Request_put___closed__0_once, _init_l_Std_Http_Request_put___closed__0);
v___x_1102_ = l_Std_Http_Request_Builder_uri(v___x_1101_, v_uri_1100_);
return v___x_1102_;
}
}
static lean_object* _init_l_Std_Http_Request_delete___closed__0(void){
_start:
{
uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = 7;
v___x_1104_ = l_Std_Http_Request_new;
v___x_1105_ = l_Std_Http_Request_Builder_method(v___x_1104_, v___x_1103_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_delete(lean_object* v_uri_1106_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_obj_once(&l_Std_Http_Request_delete___closed__0, &l_Std_Http_Request_delete___closed__0_once, _init_l_Std_Http_Request_delete___closed__0);
v___x_1108_ = l_Std_Http_Request_Builder_uri(v___x_1107_, v_uri_1106_);
return v___x_1108_;
}
}
static lean_object* _init_l_Std_Http_Request_patch___closed__0(void){
_start:
{
uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = 22;
v___x_1110_ = l_Std_Http_Request_new;
v___x_1111_ = l_Std_Http_Request_Builder_method(v___x_1110_, v___x_1109_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_patch(lean_object* v_uri_1112_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_obj_once(&l_Std_Http_Request_patch___closed__0, &l_Std_Http_Request_patch___closed__0_once, _init_l_Std_Http_Request_patch___closed__0);
v___x_1114_ = l_Std_Http_Request_Builder_uri(v___x_1113_, v_uri_1112_);
return v___x_1114_;
}
}
static lean_object* _init_l_Std_Http_Request_head___closed__0(void){
_start:
{
uint8_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = 9;
v___x_1116_ = l_Std_Http_Request_new;
v___x_1117_ = l_Std_Http_Request_Builder_method(v___x_1116_, v___x_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_head(lean_object* v_uri_1118_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_obj_once(&l_Std_Http_Request_head___closed__0, &l_Std_Http_Request_head___closed__0_once, _init_l_Std_Http_Request_head___closed__0);
v___x_1120_ = l_Std_Http_Request_Builder_uri(v___x_1119_, v_uri_1118_);
return v___x_1120_;
}
}
static lean_object* _init_l_Std_Http_Request_options___closed__0(void){
_start:
{
uint8_t v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = 20;
v___x_1122_ = l_Std_Http_Request_new;
v___x_1123_ = l_Std_Http_Request_Builder_method(v___x_1122_, v___x_1121_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_options(lean_object* v_uri_1124_){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_obj_once(&l_Std_Http_Request_options___closed__0, &l_Std_Http_Request_options___closed__0_once, _init_l_Std_Http_Request_options___closed__0);
v___x_1126_ = l_Std_Http_Request_Builder_uri(v___x_1125_, v_uri_1124_);
return v___x_1126_;
}
}
static lean_object* _init_l_Std_Http_Request_connect___closed__0(void){
_start:
{
uint8_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = 5;
v___x_1128_ = l_Std_Http_Request_new;
v___x_1129_ = l_Std_Http_Request_Builder_method(v___x_1128_, v___x_1127_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_connect(lean_object* v_uri_1130_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_obj_once(&l_Std_Http_Request_connect___closed__0, &l_Std_Http_Request_connect___closed__0_once, _init_l_Std_Http_Request_connect___closed__0);
v___x_1132_ = l_Std_Http_Request_Builder_uri(v___x_1131_, v_uri_1130_);
return v___x_1132_;
}
}
static lean_object* _init_l_Std_Http_Request_trace___closed__0(void){
_start:
{
uint8_t v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = 32;
v___x_1134_ = l_Std_Http_Request_new;
v___x_1135_ = l_Std_Http_Request_Builder_method(v___x_1134_, v___x_1133_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_trace(lean_object* v_uri_1136_){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_obj_once(&l_Std_Http_Request_trace___closed__0, &l_Std_Http_Request_trace___closed__0_once, _init_l_Std_Http_Request_trace___closed__0);
v___x_1138_ = l_Std_Http_Request_Builder_uri(v___x_1137_, v_uri_1136_);
return v___x_1138_;
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
