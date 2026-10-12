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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1;
static const lean_sarray_object l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_sarray_object) + 1, .m_other = 1, .m_tag = 248}, .m_size = 1, .m_capacity = 1, .m_data = {32}};
static const lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2 = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2_value;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3;
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
lean_object* l_Std_Http_Request_instToStringHead___lam__1(lean_object* v___x_124_, lean_object* v___x_125_, lean_object* v___x_126_, lean_object* v_fst_127_, lean_object* v___x_128_, uint32_t v___x_129_, lean_object* v___x_130_, lean_object* v_it_131_, lean_object* v_acc_132_, lean_object* v_hP_133_, lean_object* v_recur_134_){
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
LEAN_EXPORT void l_Std_Http_Request_instToStringHead___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_124_ = stack[0].m_obj;
lean_object* v___x_125_ = stack[1].m_obj;
lean_object* v___x_126_ = stack[2].m_obj;
lean_object* v_fst_127_ = stack[3].m_obj;
lean_object* v___x_128_ = stack[4].m_obj;
uint32_t v___x_129_ = stack[5].m_num;
lean_object* v___x_130_ = stack[6].m_obj;
lean_object* v_it_131_ = stack[7].m_obj;
lean_object* v_acc_132_ = stack[8].m_obj;
lean_object* v_recur_134_ = stack[10].m_obj;
lean_object* v_res_191_;
v_res_191_ = l_Std_Http_Request_instToStringHead___lam__1(v___x_124_, v___x_125_, v___x_126_, v_fst_127_, v___x_128_, v___x_129_, v___x_130_, v_it_131_, v_acc_132_, lean_box(0), v_recur_134_);
stack->m_obj
 = v_res_191_;
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__1___boxed(lean_object* v___x_192_, lean_object* v___x_193_, lean_object* v___x_194_, lean_object* v_fst_195_, lean_object* v___x_196_, lean_object* v___x_197_, lean_object* v___x_198_, lean_object* v_it_199_, lean_object* v_acc_200_, lean_object* v_hP_201_, lean_object* v_recur_202_){
_start:
{
uint32_t v___x_1520__boxed_203_; lean_object* v_res_204_; 
v___x_1520__boxed_203_ = lean_unbox_uint32(v___x_197_);
lean_dec(v___x_197_);
v_res_204_ = l_Std_Http_Request_instToStringHead___lam__1(v___x_192_, v___x_193_, v___x_194_, v_fst_195_, v___x_196_, v___x_1520__boxed_203_, v___x_198_, v_it_199_, v_acc_200_, v_hP_201_, v_recur_202_);
lean_dec_ref(v___x_198_);
lean_dec_ref(v_fst_195_);
lean_dec(v___x_194_);
lean_dec(v___x_193_);
lean_dec_ref(v___x_192_);
return v_res_204_;
}
}
static lean_object* _init_l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1(void){
_start:
{
uint32_t v___x_209_; lean_object* v___x_210_; 
v___x_209_ = 45;
v___x_210_ = lean_box_uint32(v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2(lean_object* v_x_211_){
_start:
{
lean_object* v_fst_212_; lean_object* v_snd_213_; lean_object* v___y_215_; lean_object* v___f_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_it_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___f_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_fst_212_ = lean_ctor_get(v_x_211_, 0);
lean_inc_n(v_fst_212_, 2);
v_snd_213_ = lean_ctor_get(v_x_211_, 1);
lean_inc(v_snd_213_);
lean_dec_ref(v_x_211_);
v___f_219_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__1));
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_string_utf8_byte_size(v_fst_212_);
v___x_222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_222_, 0, v_fst_212_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v___x_221_);
lean_inc_ref(v___x_222_);
v_it_223_ = l_String_Slice_splitToSubslice___redArg(v___x_222_, v___f_219_);
v___x_224_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__2));
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1;
v___f_227_ = lean_alloc_closure((void*)(l_Std_Http_Request_instToStringHead___lam__1___boxed), 11, 7);
lean_closure_set(v___f_227_, 0, v___x_224_);
lean_closure_set(v___f_227_, 1, v___x_220_);
lean_closure_set(v___f_227_, 2, v___x_225_);
lean_closure_set(v___f_227_, 3, v_fst_212_);
lean_closure_set(v___f_227_, 4, v___x_221_);
lean_closure_set(v___f_227_, 5, v___x_226_);
lean_closure_set(v___f_227_, 6, v___x_222_);
v___x_228_ = lean_box(0);
v___x_229_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_227_, v_it_223_, v___x_228_, lean_box(0));
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v___x_230_; 
v___x_230_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_215_ = v___x_230_;
goto v___jp_214_;
}
else
{
lean_object* v_val_231_; 
v_val_231_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_val_231_);
lean_dec_ref_known(v___x_229_, 1);
v___y_215_ = v_val_231_;
goto v___jp_214_;
}
v___jp_214_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__0));
v___x_217_ = lean_string_append(v___y_215_, v___x_216_);
v___x_218_ = lean_string_append(v___x_217_, v_snd_213_);
lean_dec(v_snd_213_);
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__4(lean_object* v___f_305_, lean_object* v___f_306_, lean_object* v___f_307_, lean_object* v_req_308_){
_start:
{
uint8_t v_method_309_; uint8_t v_version_310_; lean_object* v_uri_311_; lean_object* v_headers_312_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v_port_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v_host_431_; lean_object* v_port_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v_port_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v_host_466_; lean_object* v_port_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_481_; 
v_method_309_ = lean_ctor_get_uint8(v_req_308_, sizeof(void*)*2);
v_version_310_ = lean_ctor_get_uint8(v_req_308_, sizeof(void*)*2 + 1);
v_uri_311_ = lean_ctor_get(v_req_308_, 0);
lean_inc(v_uri_311_);
v_headers_312_ = lean_ctor_get(v_req_308_, 1);
lean_inc_ref(v_headers_312_);
lean_dec_ref(v_req_308_);
switch(v_method_309_)
{
case 0:
{
lean_object* v___x_553_; 
v___x_553_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__24));
v___y_481_ = v___x_553_;
goto v___jp_480_;
}
case 1:
{
lean_object* v___x_554_; 
v___x_554_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__25));
v___y_481_ = v___x_554_;
goto v___jp_480_;
}
case 2:
{
lean_object* v___x_555_; 
v___x_555_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__26));
v___y_481_ = v___x_555_;
goto v___jp_480_;
}
case 3:
{
lean_object* v___x_556_; 
v___x_556_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__27));
v___y_481_ = v___x_556_;
goto v___jp_480_;
}
case 4:
{
lean_object* v___x_557_; 
v___x_557_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__28));
v___y_481_ = v___x_557_;
goto v___jp_480_;
}
case 5:
{
lean_object* v___x_558_; 
v___x_558_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__29));
v___y_481_ = v___x_558_;
goto v___jp_480_;
}
case 6:
{
lean_object* v___x_559_; 
v___x_559_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__30));
v___y_481_ = v___x_559_;
goto v___jp_480_;
}
case 7:
{
lean_object* v___x_560_; 
v___x_560_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__31));
v___y_481_ = v___x_560_;
goto v___jp_480_;
}
case 8:
{
lean_object* v___x_561_; 
v___x_561_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__32));
v___y_481_ = v___x_561_;
goto v___jp_480_;
}
case 9:
{
lean_object* v___x_562_; 
v___x_562_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__33));
v___y_481_ = v___x_562_;
goto v___jp_480_;
}
case 10:
{
lean_object* v___x_563_; 
v___x_563_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__34));
v___y_481_ = v___x_563_;
goto v___jp_480_;
}
case 11:
{
lean_object* v___x_564_; 
v___x_564_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__35));
v___y_481_ = v___x_564_;
goto v___jp_480_;
}
case 12:
{
lean_object* v___x_565_; 
v___x_565_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__36));
v___y_481_ = v___x_565_;
goto v___jp_480_;
}
case 13:
{
lean_object* v___x_566_; 
v___x_566_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__37));
v___y_481_ = v___x_566_;
goto v___jp_480_;
}
case 14:
{
lean_object* v___x_567_; 
v___x_567_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__38));
v___y_481_ = v___x_567_;
goto v___jp_480_;
}
case 15:
{
lean_object* v___x_568_; 
v___x_568_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__39));
v___y_481_ = v___x_568_;
goto v___jp_480_;
}
case 16:
{
lean_object* v___x_569_; 
v___x_569_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__40));
v___y_481_ = v___x_569_;
goto v___jp_480_;
}
case 17:
{
lean_object* v___x_570_; 
v___x_570_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__41));
v___y_481_ = v___x_570_;
goto v___jp_480_;
}
case 18:
{
lean_object* v___x_571_; 
v___x_571_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__42));
v___y_481_ = v___x_571_;
goto v___jp_480_;
}
case 19:
{
lean_object* v___x_572_; 
v___x_572_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__43));
v___y_481_ = v___x_572_;
goto v___jp_480_;
}
case 20:
{
lean_object* v___x_573_; 
v___x_573_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__44));
v___y_481_ = v___x_573_;
goto v___jp_480_;
}
case 21:
{
lean_object* v___x_574_; 
v___x_574_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__45));
v___y_481_ = v___x_574_;
goto v___jp_480_;
}
case 22:
{
lean_object* v___x_575_; 
v___x_575_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__46));
v___y_481_ = v___x_575_;
goto v___jp_480_;
}
case 23:
{
lean_object* v___x_576_; 
v___x_576_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__47));
v___y_481_ = v___x_576_;
goto v___jp_480_;
}
case 24:
{
lean_object* v___x_577_; 
v___x_577_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__48));
v___y_481_ = v___x_577_;
goto v___jp_480_;
}
case 25:
{
lean_object* v___x_578_; 
v___x_578_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__49));
v___y_481_ = v___x_578_;
goto v___jp_480_;
}
case 26:
{
lean_object* v___x_579_; 
v___x_579_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__50));
v___y_481_ = v___x_579_;
goto v___jp_480_;
}
case 27:
{
lean_object* v___x_580_; 
v___x_580_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__51));
v___y_481_ = v___x_580_;
goto v___jp_480_;
}
case 28:
{
lean_object* v___x_581_; 
v___x_581_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__52));
v___y_481_ = v___x_581_;
goto v___jp_480_;
}
case 29:
{
lean_object* v___x_582_; 
v___x_582_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__53));
v___y_481_ = v___x_582_;
goto v___jp_480_;
}
case 30:
{
lean_object* v___x_583_; 
v___x_583_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__54));
v___y_481_ = v___x_583_;
goto v___jp_480_;
}
case 31:
{
lean_object* v___x_584_; 
v___x_584_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__55));
v___y_481_ = v___x_584_;
goto v___jp_480_;
}
case 32:
{
lean_object* v___x_585_; 
v___x_585_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__56));
v___y_481_ = v___x_585_;
goto v___jp_480_;
}
case 33:
{
lean_object* v___x_586_; 
v___x_586_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__57));
v___y_481_ = v___x_586_;
goto v___jp_480_;
}
case 34:
{
lean_object* v___x_587_; 
v___x_587_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__58));
v___y_481_ = v___x_587_;
goto v___jp_480_;
}
case 35:
{
lean_object* v___x_588_; 
v___x_588_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__59));
v___y_481_ = v___x_588_;
goto v___jp_480_;
}
case 36:
{
lean_object* v___x_589_; 
v___x_589_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__60));
v___y_481_ = v___x_589_;
goto v___jp_480_;
}
case 37:
{
lean_object* v___x_590_; 
v___x_590_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__61));
v___y_481_ = v___x_590_;
goto v___jp_480_;
}
case 38:
{
lean_object* v___x_591_; 
v___x_591_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__62));
v___y_481_ = v___x_591_;
goto v___jp_480_;
}
default: 
{
lean_object* v___x_592_; 
v___x_592_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__63));
v___y_481_ = v___x_592_;
goto v___jp_480_;
}
}
v___jp_313_:
{
lean_object* v_entries_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; size_t v_sz_321_; size_t v___x_322_; lean_object* v_pairs_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_entries_316_ = lean_ctor_get(v_headers_312_, 0);
lean_inc_ref(v_entries_316_);
lean_dec_ref(v_headers_312_);
v___x_317_ = lean_string_append(v___y_314_, v___y_315_);
v___x_318_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__0));
v___x_319_ = lean_string_append(v___x_317_, v___x_318_);
v___x_320_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_321_ = lean_array_size(v_entries_316_);
v___x_322_ = ((size_t)0ULL);
v_pairs_323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_320_, v___f_305_, v_sz_321_, v___x_322_, v_entries_316_);
v___x_324_ = lean_array_to_list(v_pairs_323_);
v___x_325_ = l_String_intercalate(v___x_318_, v___x_324_);
v___x_326_ = lean_string_append(v___x_319_, v___x_325_);
lean_dec_ref(v___x_325_);
v___x_327_ = lean_string_append(v___x_326_, v___x_318_);
return v___x_327_;
}
v___jp_328_:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_string_append(v___y_329_, v___y_331_);
lean_dec_ref(v___y_331_);
v___x_333_ = lean_string_append(v___x_332_, v___y_330_);
switch(v_version_310_)
{
case 0:
{
lean_object* v___x_334_; 
v___x_334_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__11));
v___y_314_ = v___x_333_;
v___y_315_ = v___x_334_;
goto v___jp_313_;
}
case 1:
{
lean_object* v___x_335_; 
v___x_335_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__12));
v___y_314_ = v___x_333_;
v___y_315_ = v___x_335_;
goto v___jp_313_;
}
case 2:
{
lean_object* v___x_336_; 
v___x_336_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__13));
v___y_314_ = v___x_333_;
v___y_315_ = v___x_336_;
goto v___jp_313_;
}
default: 
{
lean_object* v___x_337_; 
v___x_337_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__14));
v___y_314_ = v___x_333_;
v___y_315_ = v___x_337_;
goto v___jp_313_;
}
}
}
v___jp_338_:
{
lean_object* v_queryStr_343_; lean_object* v___x_344_; 
v_queryStr_343_ = l_Std_Http_URI_Query_formatOption(v___y_341_);
v___x_344_ = lean_string_append(v___y_342_, v_queryStr_343_);
lean_dec_ref(v_queryStr_343_);
v___y_329_ = v___y_339_;
v___y_330_ = v___y_340_;
v___y_331_ = v___x_344_;
goto v___jp_328_;
}
v___jp_345_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_353_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_354_ = lean_string_append(v___y_351_, v___x_353_);
v___x_355_ = lean_string_append(v___x_354_, v___y_349_);
lean_dec_ref(v___y_349_);
v___x_356_ = lean_string_append(v___x_355_, v___y_350_);
lean_dec_ref(v___y_350_);
v___x_357_ = lean_string_append(v___x_356_, v___y_348_);
lean_dec_ref(v___y_348_);
v___x_358_ = lean_string_append(v___x_357_, v___y_352_);
lean_dec_ref(v___y_352_);
v___y_329_ = v___y_346_;
v___y_330_ = v___y_347_;
v___y_331_ = v___x_358_;
goto v___jp_328_;
}
v___jp_359_:
{
lean_object* v_queryPart_367_; 
v_queryPart_367_ = l_Std_Http_URI_Query_formatOption(v___y_360_);
if (lean_obj_tag(v___y_363_) == 0)
{
lean_object* v___x_368_; 
v___x_368_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_346_ = v___y_361_;
v___y_347_ = v___y_362_;
v___y_348_ = v_queryPart_367_;
v___y_349_ = v___y_364_;
v___y_350_ = v___y_366_;
v___y_351_ = v___y_365_;
v___y_352_ = v___x_368_;
goto v___jp_345_;
}
else
{
lean_object* v_val_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_val_369_ = lean_ctor_get(v___y_363_, 0);
lean_inc(v_val_369_);
lean_dec_ref_known(v___y_363_, 1);
v___x_370_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__16));
v___x_371_ = l_Std_Http_URI_EncodedFragment_encode(v_val_369_);
lean_dec(v_val_369_);
v___x_372_ = lean_string_from_utf8_unchecked(v___x_371_);
v___x_373_ = lean_string_append(v___x_370_, v___x_372_);
lean_dec_ref(v___x_372_);
v___y_346_ = v___y_361_;
v___y_347_ = v___y_362_;
v___y_348_ = v_queryPart_367_;
v___y_349_ = v___y_364_;
v___y_350_ = v___y_366_;
v___y_351_ = v___y_365_;
v___y_352_ = v___x_373_;
goto v___jp_345_;
}
}
v___jp_374_:
{
lean_object* v_segments_382_; uint8_t v_absolute_383_; lean_object* v___x_384_; lean_object* v___x_385_; size_t v_sz_386_; size_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v_result_390_; 
v_segments_382_ = lean_ctor_get(v___y_379_, 0);
lean_inc_ref(v_segments_382_);
v_absolute_383_ = lean_ctor_get_uint8(v___y_379_, sizeof(void*)*1);
lean_dec_ref(v___y_379_);
v___x_384_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_385_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_386_ = lean_array_size(v_segments_382_);
v___x_387_ = ((size_t)0ULL);
v___x_388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_385_, v___f_306_, v_sz_386_, v___x_387_, v_segments_382_);
v___x_389_ = lean_array_to_list(v___x_388_);
v_result_390_ = l_String_intercalate(v___x_384_, v___x_389_);
if (v_absolute_383_ == 0)
{
v___y_360_ = v___y_375_;
v___y_361_ = v___y_376_;
v___y_362_ = v___y_377_;
v___y_363_ = v___y_378_;
v___y_364_ = v___y_381_;
v___y_365_ = v___y_380_;
v___y_366_ = v_result_390_;
goto v___jp_359_;
}
else
{
lean_object* v___x_391_; 
v___x_391_ = lean_string_append(v___x_384_, v_result_390_);
lean_dec_ref(v_result_390_);
v___y_360_ = v___y_375_;
v___y_361_ = v___y_376_;
v___y_362_ = v___y_377_;
v___y_363_ = v___y_378_;
v___y_364_ = v___y_381_;
v___y_365_ = v___y_380_;
v___y_366_ = v___x_391_;
goto v___jp_359_;
}
}
v___jp_392_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_string_append(v___y_401_, v___y_399_);
lean_dec_ref(v___y_399_);
v___x_404_ = lean_string_append(v___x_403_, v___y_402_);
lean_dec_ref(v___y_402_);
lean_inc_ref(v___y_398_);
v___x_405_ = lean_string_append(v___y_398_, v___x_404_);
lean_dec_ref(v___x_404_);
v___y_375_ = v___y_393_;
v___y_376_ = v___y_394_;
v___y_377_ = v___y_395_;
v___y_378_ = v___y_396_;
v___y_379_ = v___y_397_;
v___y_380_ = v___y_400_;
v___y_381_ = v___x_405_;
goto v___jp_374_;
}
v___jp_406_:
{
switch(lean_obj_tag(v_port_413_))
{
case 0:
{
lean_object* v___x_417_; 
v___x_417_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_393_ = v___y_407_;
v___y_394_ = v___y_408_;
v___y_395_ = v___y_409_;
v___y_396_ = v___y_410_;
v___y_397_ = v___y_411_;
v___y_398_ = v___y_412_;
v___y_399_ = v___y_416_;
v___y_400_ = v___y_415_;
v___y_401_ = v___y_414_;
v___y_402_ = v___x_417_;
goto v___jp_392_;
}
case 1:
{
lean_object* v___x_418_; 
v___x_418_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_393_ = v___y_407_;
v___y_394_ = v___y_408_;
v___y_395_ = v___y_409_;
v___y_396_ = v___y_410_;
v___y_397_ = v___y_411_;
v___y_398_ = v___y_412_;
v___y_399_ = v___y_416_;
v___y_400_ = v___y_415_;
v___y_401_ = v___y_414_;
v___y_402_ = v___x_418_;
goto v___jp_392_;
}
default: 
{
uint16_t v_port_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_port_419_ = lean_ctor_get_uint16(v_port_413_, 0);
lean_dec_ref_known(v_port_413_, 0);
v___x_420_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_421_ = lean_uint16_to_nat(v_port_419_);
v___x_422_ = l_Nat_reprFast(v___x_421_);
v___x_423_ = lean_string_append(v___x_420_, v___x_422_);
lean_dec_ref(v___x_422_);
v___y_393_ = v___y_407_;
v___y_394_ = v___y_408_;
v___y_395_ = v___y_409_;
v___y_396_ = v___y_410_;
v___y_397_ = v___y_411_;
v___y_398_ = v___y_412_;
v___y_399_ = v___y_416_;
v___y_400_ = v___y_415_;
v___y_401_ = v___y_414_;
v___y_402_ = v___x_423_;
goto v___jp_392_;
}
}
}
v___jp_424_:
{
switch(lean_obj_tag(v_host_431_))
{
case 0:
{
lean_object* v_name_435_; 
v_name_435_ = lean_ctor_get(v_host_431_, 0);
lean_inc_ref(v_name_435_);
lean_dec_ref_known(v_host_431_, 1);
v___y_407_ = v___y_425_;
v___y_408_ = v___y_426_;
v___y_409_ = v___y_427_;
v___y_410_ = v___y_428_;
v___y_411_ = v___y_429_;
v___y_412_ = v___y_430_;
v_port_413_ = v_port_432_;
v___y_414_ = v___y_434_;
v___y_415_ = v___y_433_;
v___y_416_ = v_name_435_;
goto v___jp_406_;
}
case 1:
{
lean_object* v_ipv4_436_; lean_object* v___x_437_; 
v_ipv4_436_ = lean_ctor_get(v_host_431_, 0);
lean_inc_ref(v_ipv4_436_);
lean_dec_ref_known(v_host_431_, 1);
v___x_437_ = lean_uv_ntop_v4(v_ipv4_436_);
lean_dec_ref(v_ipv4_436_);
v___y_407_ = v___y_425_;
v___y_408_ = v___y_426_;
v___y_409_ = v___y_427_;
v___y_410_ = v___y_428_;
v___y_411_ = v___y_429_;
v___y_412_ = v___y_430_;
v_port_413_ = v_port_432_;
v___y_414_ = v___y_434_;
v___y_415_ = v___y_433_;
v___y_416_ = v___x_437_;
goto v___jp_406_;
}
default: 
{
lean_object* v_ipv6_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_ipv6_438_ = lean_ctor_get(v_host_431_, 0);
lean_inc_ref(v_ipv6_438_);
lean_dec_ref_known(v_host_431_, 1);
v___x_439_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_440_ = lean_uv_ntop_v6(v_ipv6_438_);
lean_dec_ref(v_ipv6_438_);
v___x_441_ = lean_string_append(v___x_439_, v___x_440_);
lean_dec_ref(v___x_440_);
v___x_442_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_443_ = lean_string_append(v___x_441_, v___x_442_);
v___y_407_ = v___y_425_;
v___y_408_ = v___y_426_;
v___y_409_ = v___y_427_;
v___y_410_ = v___y_428_;
v___y_411_ = v___y_429_;
v___y_412_ = v___y_430_;
v_port_413_ = v_port_432_;
v___y_414_ = v___y_434_;
v___y_415_ = v___y_433_;
v___y_416_ = v___x_443_;
goto v___jp_406_;
}
}
}
v___jp_444_:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_string_append(v___y_447_, v___y_448_);
lean_dec_ref(v___y_448_);
v___x_451_ = lean_string_append(v___x_450_, v___y_449_);
lean_dec_ref(v___y_449_);
v___y_329_ = v___y_445_;
v___y_330_ = v___y_446_;
v___y_331_ = v___x_451_;
goto v___jp_328_;
}
v___jp_452_:
{
switch(lean_obj_tag(v_port_453_))
{
case 0:
{
lean_object* v___x_458_; 
v___x_458_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_445_ = v___y_454_;
v___y_446_ = v___y_455_;
v___y_447_ = v___y_456_;
v___y_448_ = v___y_457_;
v___y_449_ = v___x_458_;
goto v___jp_444_;
}
case 1:
{
lean_object* v___x_459_; 
v___x_459_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_445_ = v___y_454_;
v___y_446_ = v___y_455_;
v___y_447_ = v___y_456_;
v___y_448_ = v___y_457_;
v___y_449_ = v___x_459_;
goto v___jp_444_;
}
default: 
{
uint16_t v_port_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_port_460_ = lean_ctor_get_uint16(v_port_453_, 0);
lean_dec_ref_known(v_port_453_, 0);
v___x_461_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_462_ = lean_uint16_to_nat(v_port_460_);
v___x_463_ = l_Nat_reprFast(v___x_462_);
v___x_464_ = lean_string_append(v___x_461_, v___x_463_);
lean_dec_ref(v___x_463_);
v___y_445_ = v___y_454_;
v___y_446_ = v___y_455_;
v___y_447_ = v___y_456_;
v___y_448_ = v___y_457_;
v___y_449_ = v___x_464_;
goto v___jp_444_;
}
}
}
v___jp_465_:
{
switch(lean_obj_tag(v_host_466_))
{
case 0:
{
lean_object* v_name_471_; 
v_name_471_ = lean_ctor_get(v_host_466_, 0);
lean_inc_ref(v_name_471_);
lean_dec_ref_known(v_host_466_, 1);
v_port_453_ = v_port_467_;
v___y_454_ = v___y_468_;
v___y_455_ = v___y_469_;
v___y_456_ = v___y_470_;
v___y_457_ = v_name_471_;
goto v___jp_452_;
}
case 1:
{
lean_object* v_ipv4_472_; lean_object* v___x_473_; 
v_ipv4_472_ = lean_ctor_get(v_host_466_, 0);
lean_inc_ref(v_ipv4_472_);
lean_dec_ref_known(v_host_466_, 1);
v___x_473_ = lean_uv_ntop_v4(v_ipv4_472_);
lean_dec_ref(v_ipv4_472_);
v_port_453_ = v_port_467_;
v___y_454_ = v___y_468_;
v___y_455_ = v___y_469_;
v___y_456_ = v___y_470_;
v___y_457_ = v___x_473_;
goto v___jp_452_;
}
default: 
{
lean_object* v_ipv6_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_ipv6_474_ = lean_ctor_get(v_host_466_, 0);
lean_inc_ref(v_ipv6_474_);
lean_dec_ref_known(v_host_466_, 1);
v___x_475_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_476_ = lean_uv_ntop_v6(v_ipv6_474_);
lean_dec_ref(v_ipv6_474_);
v___x_477_ = lean_string_append(v___x_475_, v___x_476_);
lean_dec_ref(v___x_476_);
v___x_478_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_479_ = lean_string_append(v___x_477_, v___x_478_);
v_port_453_ = v_port_467_;
v___y_454_ = v___y_468_;
v___y_455_ = v___y_469_;
v___y_456_ = v___y_470_;
v___y_457_ = v___x_479_;
goto v___jp_452_;
}
}
}
v___jp_480_:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__20));
lean_inc_ref(v___y_481_);
v___x_483_ = lean_string_append(v___y_481_, v___x_482_);
switch(lean_obj_tag(v_uri_311_))
{
case 0:
{
lean_object* v_path_484_; lean_object* v_query_485_; lean_object* v_segments_486_; uint8_t v_absolute_487_; lean_object* v___x_488_; lean_object* v___x_489_; size_t v_sz_490_; size_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_result_494_; 
lean_dec_ref(v___f_306_);
v_path_484_ = lean_ctor_get(v_uri_311_, 0);
lean_inc_ref(v_path_484_);
v_query_485_ = lean_ctor_get(v_uri_311_, 1);
lean_inc(v_query_485_);
lean_dec_ref_known(v_uri_311_, 2);
v_segments_486_ = lean_ctor_get(v_path_484_, 0);
lean_inc_ref(v_segments_486_);
v_absolute_487_ = lean_ctor_get_uint8(v_path_484_, sizeof(void*)*1);
lean_dec_ref(v_path_484_);
v___x_488_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_489_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_490_ = lean_array_size(v_segments_486_);
v___x_491_ = ((size_t)0ULL);
v___x_492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_489_, v___f_307_, v_sz_490_, v___x_491_, v_segments_486_);
v___x_493_ = lean_array_to_list(v___x_492_);
v_result_494_ = l_String_intercalate(v___x_488_, v___x_493_);
if (v_absolute_487_ == 0)
{
v___y_339_ = v___x_483_;
v___y_340_ = v___x_482_;
v___y_341_ = v_query_485_;
v___y_342_ = v_result_494_;
goto v___jp_338_;
}
else
{
lean_object* v___x_495_; 
v___x_495_ = lean_string_append(v___x_488_, v_result_494_);
lean_dec_ref(v_result_494_);
v___y_339_ = v___x_483_;
v___y_340_ = v___x_482_;
v___y_341_ = v_query_485_;
v___y_342_ = v___x_495_;
goto v___jp_338_;
}
}
case 1:
{
lean_object* v_uri_496_; lean_object* v_authority_497_; 
lean_dec_ref(v___f_307_);
v_uri_496_ = lean_ctor_get(v_uri_311_, 0);
lean_inc_ref(v_uri_496_);
lean_dec_ref_known(v_uri_311_, 1);
v_authority_497_ = lean_ctor_get(v_uri_496_, 1);
if (lean_obj_tag(v_authority_497_) == 0)
{
lean_object* v_scheme_498_; lean_object* v_path_499_; lean_object* v_query_500_; lean_object* v_fragment_501_; lean_object* v___x_502_; 
v_scheme_498_ = lean_ctor_get(v_uri_496_, 0);
lean_inc_ref(v_scheme_498_);
v_path_499_ = lean_ctor_get(v_uri_496_, 2);
lean_inc_ref(v_path_499_);
v_query_500_ = lean_ctor_get(v_uri_496_, 3);
lean_inc(v_query_500_);
v_fragment_501_ = lean_ctor_get(v_uri_496_, 4);
lean_inc(v_fragment_501_);
lean_dec_ref(v_uri_496_);
v___x_502_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_375_ = v_query_500_;
v___y_376_ = v___x_483_;
v___y_377_ = v___x_482_;
v___y_378_ = v_fragment_501_;
v___y_379_ = v_path_499_;
v___y_380_ = v_scheme_498_;
v___y_381_ = v___x_502_;
goto v___jp_374_;
}
else
{
lean_object* v_val_503_; lean_object* v_scheme_504_; lean_object* v_path_505_; lean_object* v_query_506_; lean_object* v_fragment_507_; lean_object* v_userInfo_508_; lean_object* v_host_509_; lean_object* v_port_510_; lean_object* v___x_511_; 
v_val_503_ = lean_ctor_get(v_authority_497_, 0);
lean_inc(v_val_503_);
v_scheme_504_ = lean_ctor_get(v_uri_496_, 0);
lean_inc_ref(v_scheme_504_);
v_path_505_ = lean_ctor_get(v_uri_496_, 2);
lean_inc_ref(v_path_505_);
v_query_506_ = lean_ctor_get(v_uri_496_, 3);
lean_inc(v_query_506_);
v_fragment_507_ = lean_ctor_get(v_uri_496_, 4);
lean_inc(v_fragment_507_);
lean_dec_ref(v_uri_496_);
v_userInfo_508_ = lean_ctor_get(v_val_503_, 0);
lean_inc(v_userInfo_508_);
v_host_509_ = lean_ctor_get(v_val_503_, 1);
lean_inc_ref(v_host_509_);
v_port_510_ = lean_ctor_get(v_val_503_, 2);
lean_inc(v_port_510_);
lean_dec(v_val_503_);
v___x_511_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__21));
if (lean_obj_tag(v_userInfo_508_) == 0)
{
lean_object* v___x_512_; 
v___x_512_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_425_ = v_query_506_;
v___y_426_ = v___x_483_;
v___y_427_ = v___x_482_;
v___y_428_ = v_fragment_507_;
v___y_429_ = v_path_505_;
v___y_430_ = v___x_511_;
v_host_431_ = v_host_509_;
v_port_432_ = v_port_510_;
v___y_433_ = v_scheme_504_;
v___y_434_ = v___x_512_;
goto v___jp_424_;
}
else
{
lean_object* v_val_513_; lean_object* v_password_514_; 
v_val_513_ = lean_ctor_get(v_userInfo_508_, 0);
lean_inc(v_val_513_);
lean_dec_ref_known(v_userInfo_508_, 1);
v_password_514_ = lean_ctor_get(v_val_513_, 1);
if (lean_obj_tag(v_password_514_) == 0)
{
lean_object* v_username_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_username_515_ = lean_ctor_get(v_val_513_, 0);
lean_inc_ref(v_username_515_);
lean_dec(v_val_513_);
v___x_516_ = lean_string_from_utf8_unchecked(v_username_515_);
v___x_517_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_518_ = lean_string_append(v___x_516_, v___x_517_);
v___y_425_ = v_query_506_;
v___y_426_ = v___x_483_;
v___y_427_ = v___x_482_;
v___y_428_ = v_fragment_507_;
v___y_429_ = v_path_505_;
v___y_430_ = v___x_511_;
v_host_431_ = v_host_509_;
v_port_432_ = v_port_510_;
v___y_433_ = v_scheme_504_;
v___y_434_ = v___x_518_;
goto v___jp_424_;
}
else
{
lean_object* v_username_519_; lean_object* v_val_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
lean_inc_ref(v_password_514_);
v_username_519_ = lean_ctor_get(v_val_513_, 0);
lean_inc_ref(v_username_519_);
lean_dec(v_val_513_);
v_val_520_ = lean_ctor_get(v_password_514_, 0);
lean_inc(v_val_520_);
lean_dec_ref_known(v_password_514_, 1);
v___x_521_ = lean_string_from_utf8_unchecked(v_username_519_);
v___x_522_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_523_ = lean_string_append(v___x_521_, v___x_522_);
v___x_524_ = lean_string_from_utf8_unchecked(v_val_520_);
v___x_525_ = lean_string_append(v___x_523_, v___x_524_);
lean_dec_ref(v___x_524_);
v___x_526_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_527_ = lean_string_append(v___x_525_, v___x_526_);
v___y_425_ = v_query_506_;
v___y_426_ = v___x_483_;
v___y_427_ = v___x_482_;
v___y_428_ = v_fragment_507_;
v___y_429_ = v_path_505_;
v___y_430_ = v___x_511_;
v_host_431_ = v_host_509_;
v_port_432_ = v_port_510_;
v___y_433_ = v_scheme_504_;
v___y_434_ = v___x_527_;
goto v___jp_424_;
}
}
}
}
case 2:
{
lean_object* v_authority_528_; lean_object* v_userInfo_529_; 
lean_dec_ref(v___f_307_);
lean_dec_ref(v___f_306_);
v_authority_528_ = lean_ctor_get(v_uri_311_, 0);
lean_inc_ref(v_authority_528_);
lean_dec_ref_known(v_uri_311_, 1);
v_userInfo_529_ = lean_ctor_get(v_authority_528_, 0);
if (lean_obj_tag(v_userInfo_529_) == 0)
{
lean_object* v_host_530_; lean_object* v_port_531_; lean_object* v___x_532_; 
v_host_530_ = lean_ctor_get(v_authority_528_, 1);
lean_inc_ref(v_host_530_);
v_port_531_ = lean_ctor_get(v_authority_528_, 2);
lean_inc(v_port_531_);
lean_dec_ref(v_authority_528_);
v___x_532_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v_host_466_ = v_host_530_;
v_port_467_ = v_port_531_;
v___y_468_ = v___x_483_;
v___y_469_ = v___x_482_;
v___y_470_ = v___x_532_;
goto v___jp_465_;
}
else
{
lean_object* v_val_533_; lean_object* v_password_534_; 
v_val_533_ = lean_ctor_get(v_userInfo_529_, 0);
lean_inc(v_val_533_);
v_password_534_ = lean_ctor_get(v_val_533_, 1);
if (lean_obj_tag(v_password_534_) == 0)
{
lean_object* v_host_535_; lean_object* v_port_536_; lean_object* v_username_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_host_535_ = lean_ctor_get(v_authority_528_, 1);
lean_inc_ref(v_host_535_);
v_port_536_ = lean_ctor_get(v_authority_528_, 2);
lean_inc(v_port_536_);
lean_dec_ref(v_authority_528_);
v_username_537_ = lean_ctor_get(v_val_533_, 0);
lean_inc_ref(v_username_537_);
lean_dec(v_val_533_);
v___x_538_ = lean_string_from_utf8_unchecked(v_username_537_);
v___x_539_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_540_ = lean_string_append(v___x_538_, v___x_539_);
v_host_466_ = v_host_535_;
v_port_467_ = v_port_536_;
v___y_468_ = v___x_483_;
v___y_469_ = v___x_482_;
v___y_470_ = v___x_540_;
goto v___jp_465_;
}
else
{
lean_object* v_host_541_; lean_object* v_port_542_; lean_object* v_username_543_; lean_object* v_val_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
lean_inc_ref(v_password_534_);
v_host_541_ = lean_ctor_get(v_authority_528_, 1);
lean_inc_ref(v_host_541_);
v_port_542_ = lean_ctor_get(v_authority_528_, 2);
lean_inc(v_port_542_);
lean_dec_ref(v_authority_528_);
v_username_543_ = lean_ctor_get(v_val_533_, 0);
lean_inc_ref(v_username_543_);
lean_dec(v_val_533_);
v_val_544_ = lean_ctor_get(v_password_534_, 0);
lean_inc(v_val_544_);
lean_dec_ref_known(v_password_534_, 1);
v___x_545_ = lean_string_from_utf8_unchecked(v_username_543_);
v___x_546_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_547_ = lean_string_append(v___x_545_, v___x_546_);
v___x_548_ = lean_string_from_utf8_unchecked(v_val_544_);
v___x_549_ = lean_string_append(v___x_547_, v___x_548_);
lean_dec_ref(v___x_548_);
v___x_550_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_551_ = lean_string_append(v___x_549_, v___x_550_);
v_host_466_ = v_host_541_;
v_port_467_ = v_port_542_;
v___y_468_ = v___x_483_;
v___y_469_ = v___x_482_;
v___y_470_ = v___x_551_;
goto v___jp_465_;
}
}
}
default: 
{
lean_object* v___x_552_; 
lean_dec_ref(v___f_307_);
lean_dec_ref(v___f_306_);
v___x_552_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__23));
v___y_329_ = v___x_483_;
v___y_330_ = v___x_482_;
v___y_331_ = v___x_552_;
goto v___jp_328_;
}
}
}
}
}
lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1(lean_object* v___x_599_, lean_object* v___x_600_, lean_object* v___x_601_, lean_object* v_name_602_, lean_object* v___x_603_, uint32_t v___x_604_, lean_object* v___x_605_, lean_object* v_it_606_, lean_object* v_acc_607_, lean_object* v_hP_608_, lean_object* v_recur_609_){
_start:
{
lean_object* v_it_611_; lean_object* v_out_612_; lean_object* v_it_628_; lean_object* v_startInclusive_629_; lean_object* v_endExclusive_630_; 
if (lean_obj_tag(v_it_606_) == 0)
{
lean_object* v_currPos_642_; lean_object* v_searcher_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_665_; 
v_currPos_642_ = lean_ctor_get(v_it_606_, 0);
v_searcher_643_ = lean_ctor_get(v_it_606_, 1);
v_isSharedCheck_665_ = !lean_is_exclusive(v_it_606_);
if (v_isSharedCheck_665_ == 0)
{
v___x_645_ = v_it_606_;
v_isShared_646_ = v_isSharedCheck_665_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_searcher_643_);
lean_inc(v_currPos_642_);
lean_dec(v_it_606_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_665_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
uint8_t v_decide_647_; 
v_decide_647_ = lean_nat_dec_eq(v_searcher_643_, v___x_603_);
if (v_decide_647_ == 0)
{
uint32_t v___x_648_; uint8_t v___x_649_; 
lean_dec(v___x_603_);
v___x_648_ = lean_string_utf8_get_fast(v_name_602_, v_searcher_643_);
v___x_649_ = lean_uint32_dec_eq(v___x_648_, v___x_604_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = lean_string_utf8_next_fast(v_name_602_, v_searcher_643_);
lean_dec(v_searcher_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v___x_650_);
v___x_652_ = v___x_645_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_currPos_642_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v___x_650_);
v___x_652_ = v_reuseFailAlloc_654_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_653_; 
v___x_653_ = lean_apply_4(v_recur_609_, v___x_652_, v_acc_607_, lean_box(0), lean_box(0));
return v___x_653_;
}
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v_slice_658_; lean_object* v_nextIt_660_; 
v___x_655_ = lean_string_utf8_next_fast(v_name_602_, v_searcher_643_);
v___x_656_ = lean_nat_sub(v___x_655_, v_searcher_643_);
v___x_657_ = lean_nat_add(v_searcher_643_, v___x_656_);
lean_dec(v___x_656_);
v_slice_658_ = l_String_Slice_subslice_x21(v___x_605_, v_currPos_642_, v_searcher_643_);
lean_inc(v___x_657_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v___x_657_);
lean_ctor_set(v___x_645_, 0, v___x_657_);
v_nextIt_660_ = v___x_645_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_657_);
v_nextIt_660_ = v_reuseFailAlloc_663_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v_startInclusive_661_; lean_object* v_endExclusive_662_; 
v_startInclusive_661_ = lean_ctor_get(v_slice_658_, 0);
lean_inc(v_startInclusive_661_);
v_endExclusive_662_ = lean_ctor_get(v_slice_658_, 1);
lean_inc(v_endExclusive_662_);
lean_dec_ref(v_slice_658_);
v_it_628_ = v_nextIt_660_;
v_startInclusive_629_ = v_startInclusive_661_;
v_endExclusive_630_ = v_endExclusive_662_;
goto v___jp_627_;
}
}
}
else
{
lean_object* v___x_664_; 
lean_del_object(v___x_645_);
lean_dec(v_searcher_643_);
v___x_664_ = lean_box(1);
v_it_628_ = v___x_664_;
v_startInclusive_629_ = v_currPos_642_;
v_endExclusive_630_ = v___x_603_;
goto v___jp_627_;
}
}
}
else
{
lean_dec_ref(v_recur_609_);
lean_dec(v___x_603_);
return v_acc_607_;
}
v___jp_610_:
{
if (lean_obj_tag(v_acc_607_) == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v_out_612_);
v___x_614_ = lean_apply_4(v_recur_609_, v_it_611_, v___x_613_, lean_box(0), lean_box(0));
return v___x_614_;
}
else
{
lean_object* v_val_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_626_; 
v_val_615_ = lean_ctor_get(v_acc_607_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v_acc_607_);
if (v_isSharedCheck_626_ == 0)
{
v___x_617_ = v_acc_607_;
v_isShared_618_ = v_isSharedCheck_626_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_val_615_);
lean_dec(v_acc_607_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_626_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_619_ = lean_string_utf8_extract_fast(v___x_599_, v___x_600_, v___x_601_);
v___x_620_ = lean_string_append(v_val_615_, v___x_619_);
lean_dec_ref(v___x_619_);
v___x_621_ = lean_string_append(v___x_620_, v_out_612_);
lean_dec_ref(v_out_612_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_621_);
v___x_623_ = v___x_617_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_625_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; 
v___x_624_ = lean_apply_4(v_recur_609_, v_it_611_, v___x_623_, lean_box(0), lean_box(0));
return v___x_624_;
}
}
}
}
v___jp_627_:
{
lean_object* v___x_631_; uint32_t v___x_632_; uint32_t v___x_633_; uint8_t v___x_634_; 
v___x_631_ = lean_string_utf8_extract_fast(v_name_602_, v_startInclusive_629_, v_endExclusive_630_);
lean_dec(v_endExclusive_630_);
lean_dec(v_startInclusive_629_);
v___x_632_ = lean_string_utf8_get(v___x_631_, v___x_600_);
v___x_633_ = 97;
v___x_634_ = lean_uint32_dec_le(v___x_633_, v___x_632_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
v___x_635_ = lean_string_utf8_set(v___x_631_, v___x_600_, v___x_632_);
v_it_611_ = v_it_628_;
v_out_612_ = v___x_635_;
goto v___jp_610_;
}
else
{
uint32_t v___x_636_; uint8_t v___x_637_; 
v___x_636_ = 122;
v___x_637_ = lean_uint32_dec_le(v___x_632_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_string_utf8_set(v___x_631_, v___x_600_, v___x_632_);
v_it_611_ = v_it_628_;
v_out_612_ = v___x_638_;
goto v___jp_610_;
}
else
{
uint32_t v___x_639_; uint32_t v___x_640_; lean_object* v___x_641_; 
v___x_639_ = 4294967264;
v___x_640_ = lean_uint32_add(v___x_632_, v___x_639_);
v___x_641_ = lean_string_utf8_set(v___x_631_, v___x_600_, v___x_640_);
v_it_611_ = v_it_628_;
v_out_612_ = v___x_641_;
goto v___jp_610_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Request_instEncodeV11Head___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_599_ = stack[0].m_obj;
lean_object* v___x_600_ = stack[1].m_obj;
lean_object* v___x_601_ = stack[2].m_obj;
lean_object* v_name_602_ = stack[3].m_obj;
lean_object* v___x_603_ = stack[4].m_obj;
uint32_t v___x_604_ = stack[5].m_num;
lean_object* v___x_605_ = stack[6].m_obj;
lean_object* v_it_606_ = stack[7].m_obj;
lean_object* v_acc_607_ = stack[8].m_obj;
lean_object* v_recur_609_ = stack[10].m_obj;
lean_object* v_res_666_;
v_res_666_ = l_Std_Http_Request_instEncodeV11Head___lam__1(v___x_599_, v___x_600_, v___x_601_, v_name_602_, v___x_603_, v___x_604_, v___x_605_, v_it_606_, v_acc_607_, lean_box(0), v_recur_609_);
stack->m_obj
 = v_res_666_;
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1___boxed(lean_object* v___x_667_, lean_object* v___x_668_, lean_object* v___x_669_, lean_object* v_name_670_, lean_object* v___x_671_, lean_object* v___x_672_, lean_object* v___x_673_, lean_object* v_it_674_, lean_object* v_acc_675_, lean_object* v_hP_676_, lean_object* v_recur_677_){
_start:
{
uint32_t v___x_3057__boxed_678_; lean_object* v_res_679_; 
v___x_3057__boxed_678_ = lean_unbox_uint32(v___x_672_);
lean_dec(v___x_672_);
v_res_679_ = l_Std_Http_Request_instEncodeV11Head___lam__1(v___x_667_, v___x_668_, v___x_669_, v_name_670_, v___x_671_, v___x_3057__boxed_678_, v___x_673_, v_it_674_, v_acc_675_, v_hP_676_, v_recur_677_);
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
v___x_709_ = lean_unsigned_to_nat(1u);
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
v___x_714_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
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
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = ((lean_object*)(l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2));
v___x_731_ = lean_byte_array_size(v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3(lean_object* v___f_732_, lean_object* v___f_733_, lean_object* v___f_734_, lean_object* v_buffer_735_, lean_object* v_req_736_){
_start:
{
uint8_t v_method_737_; uint8_t v_version_738_; lean_object* v_uri_739_; lean_object* v_headers_740_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v_port_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_808_; lean_object* v_host_809_; lean_object* v_port_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v_port_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v_host_920_; lean_object* v_port_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_945_; 
v_method_737_ = lean_ctor_get_uint8(v_req_736_, sizeof(void*)*2);
v_version_738_ = lean_ctor_get_uint8(v_req_736_, sizeof(void*)*2 + 1);
v_uri_739_ = lean_ctor_get(v_req_736_, 0);
lean_inc(v_uri_739_);
v_headers_740_ = lean_ctor_get(v_req_736_, 1);
lean_inc_ref(v_headers_740_);
lean_dec_ref(v_req_736_);
switch(v_method_737_)
{
case 0:
{
lean_object* v___x_1025_; 
v___x_1025_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__24));
v___y_945_ = v___x_1025_;
goto v___jp_944_;
}
case 1:
{
lean_object* v___x_1026_; 
v___x_1026_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__25));
v___y_945_ = v___x_1026_;
goto v___jp_944_;
}
case 2:
{
lean_object* v___x_1027_; 
v___x_1027_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__26));
v___y_945_ = v___x_1027_;
goto v___jp_944_;
}
case 3:
{
lean_object* v___x_1028_; 
v___x_1028_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__27));
v___y_945_ = v___x_1028_;
goto v___jp_944_;
}
case 4:
{
lean_object* v___x_1029_; 
v___x_1029_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__28));
v___y_945_ = v___x_1029_;
goto v___jp_944_;
}
case 5:
{
lean_object* v___x_1030_; 
v___x_1030_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__29));
v___y_945_ = v___x_1030_;
goto v___jp_944_;
}
case 6:
{
lean_object* v___x_1031_; 
v___x_1031_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__30));
v___y_945_ = v___x_1031_;
goto v___jp_944_;
}
case 7:
{
lean_object* v___x_1032_; 
v___x_1032_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__31));
v___y_945_ = v___x_1032_;
goto v___jp_944_;
}
case 8:
{
lean_object* v___x_1033_; 
v___x_1033_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__32));
v___y_945_ = v___x_1033_;
goto v___jp_944_;
}
case 9:
{
lean_object* v___x_1034_; 
v___x_1034_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__33));
v___y_945_ = v___x_1034_;
goto v___jp_944_;
}
case 10:
{
lean_object* v___x_1035_; 
v___x_1035_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__34));
v___y_945_ = v___x_1035_;
goto v___jp_944_;
}
case 11:
{
lean_object* v___x_1036_; 
v___x_1036_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__35));
v___y_945_ = v___x_1036_;
goto v___jp_944_;
}
case 12:
{
lean_object* v___x_1037_; 
v___x_1037_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__36));
v___y_945_ = v___x_1037_;
goto v___jp_944_;
}
case 13:
{
lean_object* v___x_1038_; 
v___x_1038_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__37));
v___y_945_ = v___x_1038_;
goto v___jp_944_;
}
case 14:
{
lean_object* v___x_1039_; 
v___x_1039_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__38));
v___y_945_ = v___x_1039_;
goto v___jp_944_;
}
case 15:
{
lean_object* v___x_1040_; 
v___x_1040_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__39));
v___y_945_ = v___x_1040_;
goto v___jp_944_;
}
case 16:
{
lean_object* v___x_1041_; 
v___x_1041_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__40));
v___y_945_ = v___x_1041_;
goto v___jp_944_;
}
case 17:
{
lean_object* v___x_1042_; 
v___x_1042_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__41));
v___y_945_ = v___x_1042_;
goto v___jp_944_;
}
case 18:
{
lean_object* v___x_1043_; 
v___x_1043_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__42));
v___y_945_ = v___x_1043_;
goto v___jp_944_;
}
case 19:
{
lean_object* v___x_1044_; 
v___x_1044_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__43));
v___y_945_ = v___x_1044_;
goto v___jp_944_;
}
case 20:
{
lean_object* v___x_1045_; 
v___x_1045_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__44));
v___y_945_ = v___x_1045_;
goto v___jp_944_;
}
case 21:
{
lean_object* v___x_1046_; 
v___x_1046_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__45));
v___y_945_ = v___x_1046_;
goto v___jp_944_;
}
case 22:
{
lean_object* v___x_1047_; 
v___x_1047_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__46));
v___y_945_ = v___x_1047_;
goto v___jp_944_;
}
case 23:
{
lean_object* v___x_1048_; 
v___x_1048_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__47));
v___y_945_ = v___x_1048_;
goto v___jp_944_;
}
case 24:
{
lean_object* v___x_1049_; 
v___x_1049_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__48));
v___y_945_ = v___x_1049_;
goto v___jp_944_;
}
case 25:
{
lean_object* v___x_1050_; 
v___x_1050_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__49));
v___y_945_ = v___x_1050_;
goto v___jp_944_;
}
case 26:
{
lean_object* v___x_1051_; 
v___x_1051_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__50));
v___y_945_ = v___x_1051_;
goto v___jp_944_;
}
case 27:
{
lean_object* v___x_1052_; 
v___x_1052_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__51));
v___y_945_ = v___x_1052_;
goto v___jp_944_;
}
case 28:
{
lean_object* v___x_1053_; 
v___x_1053_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__52));
v___y_945_ = v___x_1053_;
goto v___jp_944_;
}
case 29:
{
lean_object* v___x_1054_; 
v___x_1054_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__53));
v___y_945_ = v___x_1054_;
goto v___jp_944_;
}
case 30:
{
lean_object* v___x_1055_; 
v___x_1055_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__54));
v___y_945_ = v___x_1055_;
goto v___jp_944_;
}
case 31:
{
lean_object* v___x_1056_; 
v___x_1056_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__55));
v___y_945_ = v___x_1056_;
goto v___jp_944_;
}
case 32:
{
lean_object* v___x_1057_; 
v___x_1057_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__56));
v___y_945_ = v___x_1057_;
goto v___jp_944_;
}
case 33:
{
lean_object* v___x_1058_; 
v___x_1058_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__57));
v___y_945_ = v___x_1058_;
goto v___jp_944_;
}
case 34:
{
lean_object* v___x_1059_; 
v___x_1059_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__58));
v___y_945_ = v___x_1059_;
goto v___jp_944_;
}
case 35:
{
lean_object* v___x_1060_; 
v___x_1060_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__59));
v___y_945_ = v___x_1060_;
goto v___jp_944_;
}
case 36:
{
lean_object* v___x_1061_; 
v___x_1061_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__60));
v___y_945_ = v___x_1061_;
goto v___jp_944_;
}
case 37:
{
lean_object* v___x_1062_; 
v___x_1062_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__61));
v___y_945_ = v___x_1062_;
goto v___jp_944_;
}
case 38:
{
lean_object* v___x_1063_; 
v___x_1063_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__62));
v___y_945_ = v___x_1063_;
goto v___jp_944_;
}
default: 
{
lean_object* v___x_1064_; 
v___x_1064_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__63));
v___y_945_ = v___x_1064_;
goto v___jp_944_;
}
}
v___jp_741_:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v_buffer_753_; lean_object* v_buffer_754_; lean_object* v_data_755_; lean_object* v_size_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_765_; 
v___x_745_ = lean_string_to_utf8(v___y_744_);
lean_inc_ref(v___x_745_);
v___x_746_ = lean_array_push(v___y_743_, v___x_745_);
v___x_747_ = lean_byte_array_size(v___x_745_);
lean_dec_ref(v___x_745_);
v___x_748_ = lean_nat_add(v___y_742_, v___x_747_);
lean_dec(v___y_742_);
v___x_749_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0);
v___x_750_ = lean_array_push(v___x_746_, v___x_749_);
v___x_751_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1);
v___x_752_ = lean_nat_add(v___x_748_, v___x_751_);
lean_dec(v___x_748_);
v_buffer_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_753_, 0, v___x_750_);
lean_ctor_set(v_buffer_753_, 1, v___x_752_);
v_buffer_754_ = l_Std_Http_Headers_fold___redArg(v_headers_740_, v_buffer_753_, v___f_732_);
lean_dec_ref(v_headers_740_);
v_data_755_ = lean_ctor_get(v_buffer_754_, 0);
v_size_756_ = lean_ctor_get(v_buffer_754_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_buffer_754_);
if (v_isSharedCheck_765_ == 0)
{
v___x_758_ = v_buffer_754_;
v_isShared_759_ = v_isSharedCheck_765_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_size_756_);
lean_inc(v_data_755_);
lean_dec(v_buffer_754_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_765_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_760_ = lean_array_push(v_data_755_, v___x_749_);
v___x_761_ = lean_nat_add(v_size_756_, v___x_751_);
lean_dec(v_size_756_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v___x_761_);
lean_ctor_set(v___x_758_, 0, v___x_760_);
v___x_763_ = v___x_758_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
v___jp_766_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_772_ = lean_string_to_utf8(v___y_771_);
lean_dec_ref(v___y_771_);
lean_inc_ref(v___x_772_);
v___x_773_ = lean_array_push(v___y_767_, v___x_772_);
v___x_774_ = lean_byte_array_size(v___x_772_);
lean_dec_ref(v___x_772_);
v___x_775_ = lean_nat_add(v___y_769_, v___x_774_);
lean_dec(v___y_769_);
v___x_776_ = lean_array_push(v___x_773_, v___y_768_);
v___x_777_ = lean_nat_add(v___x_775_, v___y_770_);
lean_dec(v___x_775_);
switch(v_version_738_)
{
case 0:
{
lean_object* v___x_778_; 
v___x_778_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__11));
v___y_742_ = v___x_777_;
v___y_743_ = v___x_776_;
v___y_744_ = v___x_778_;
goto v___jp_741_;
}
case 1:
{
lean_object* v___x_779_; 
v___x_779_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__12));
v___y_742_ = v___x_777_;
v___y_743_ = v___x_776_;
v___y_744_ = v___x_779_;
goto v___jp_741_;
}
case 2:
{
lean_object* v___x_780_; 
v___x_780_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__13));
v___y_742_ = v___x_777_;
v___y_743_ = v___x_776_;
v___y_744_ = v___x_780_;
goto v___jp_741_;
}
default: 
{
lean_object* v___x_781_; 
v___x_781_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__14));
v___y_742_ = v___x_777_;
v___y_743_ = v___x_776_;
v___y_744_ = v___x_781_;
goto v___jp_741_;
}
}
}
v___jp_782_:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_string_append(v___y_785_, v___y_788_);
lean_dec_ref(v___y_788_);
v___x_791_ = lean_string_append(v___x_790_, v___y_789_);
lean_dec_ref(v___y_789_);
v___y_767_ = v___y_783_;
v___y_768_ = v___y_784_;
v___y_769_ = v___y_786_;
v___y_770_ = v___y_787_;
v___y_771_ = v___x_791_;
goto v___jp_766_;
}
v___jp_792_:
{
switch(lean_obj_tag(v_port_793_))
{
case 0:
{
lean_object* v___x_800_; 
v___x_800_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_783_ = v___y_794_;
v___y_784_ = v___y_796_;
v___y_785_ = v___y_795_;
v___y_786_ = v___y_797_;
v___y_787_ = v___y_798_;
v___y_788_ = v___y_799_;
v___y_789_ = v___x_800_;
goto v___jp_782_;
}
case 1:
{
lean_object* v___x_801_; 
v___x_801_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_783_ = v___y_794_;
v___y_784_ = v___y_796_;
v___y_785_ = v___y_795_;
v___y_786_ = v___y_797_;
v___y_787_ = v___y_798_;
v___y_788_ = v___y_799_;
v___y_789_ = v___x_801_;
goto v___jp_782_;
}
default: 
{
uint16_t v_port_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v_port_802_ = lean_ctor_get_uint16(v_port_793_, 0);
lean_dec_ref_known(v_port_793_, 0);
v___x_803_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_804_ = lean_uint16_to_nat(v_port_802_);
v___x_805_ = l_Nat_reprFast(v___x_804_);
v___x_806_ = lean_string_append(v___x_803_, v___x_805_);
lean_dec_ref(v___x_805_);
v___y_783_ = v___y_794_;
v___y_784_ = v___y_796_;
v___y_785_ = v___y_795_;
v___y_786_ = v___y_797_;
v___y_787_ = v___y_798_;
v___y_788_ = v___y_799_;
v___y_789_ = v___x_806_;
goto v___jp_782_;
}
}
}
v___jp_807_:
{
switch(lean_obj_tag(v_host_809_))
{
case 0:
{
lean_object* v_name_815_; 
v_name_815_ = lean_ctor_get(v_host_809_, 0);
lean_inc_ref(v_name_815_);
lean_dec_ref_known(v_host_809_, 1);
v_port_793_ = v_port_810_;
v___y_794_ = v___y_808_;
v___y_795_ = v___y_814_;
v___y_796_ = v___y_811_;
v___y_797_ = v___y_812_;
v___y_798_ = v___y_813_;
v___y_799_ = v_name_815_;
goto v___jp_792_;
}
case 1:
{
lean_object* v_ipv4_816_; lean_object* v___x_817_; 
v_ipv4_816_ = lean_ctor_get(v_host_809_, 0);
lean_inc_ref(v_ipv4_816_);
lean_dec_ref_known(v_host_809_, 1);
v___x_817_ = lean_uv_ntop_v4(v_ipv4_816_);
lean_dec_ref(v_ipv4_816_);
v_port_793_ = v_port_810_;
v___y_794_ = v___y_808_;
v___y_795_ = v___y_814_;
v___y_796_ = v___y_811_;
v___y_797_ = v___y_812_;
v___y_798_ = v___y_813_;
v___y_799_ = v___x_817_;
goto v___jp_792_;
}
default: 
{
lean_object* v_ipv6_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v_ipv6_818_ = lean_ctor_get(v_host_809_, 0);
lean_inc_ref(v_ipv6_818_);
lean_dec_ref_known(v_host_809_, 1);
v___x_819_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_820_ = lean_uv_ntop_v6(v_ipv6_818_);
lean_dec_ref(v_ipv6_818_);
v___x_821_ = lean_string_append(v___x_819_, v___x_820_);
lean_dec_ref(v___x_820_);
v___x_822_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_823_ = lean_string_append(v___x_821_, v___x_822_);
v_port_793_ = v_port_810_;
v___y_794_ = v___y_808_;
v___y_795_ = v___y_814_;
v___y_796_ = v___y_811_;
v___y_797_ = v___y_812_;
v___y_798_ = v___y_813_;
v___y_799_ = v___x_823_;
goto v___jp_792_;
}
}
}
v___jp_824_:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_834_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_835_ = lean_string_append(v___y_827_, v___x_834_);
v___x_836_ = lean_string_append(v___x_835_, v___y_829_);
lean_dec_ref(v___y_829_);
v___x_837_ = lean_string_append(v___x_836_, v___y_832_);
lean_dec_ref(v___y_832_);
v___x_838_ = lean_string_append(v___x_837_, v___y_831_);
lean_dec_ref(v___y_831_);
v___x_839_ = lean_string_append(v___x_838_, v___y_833_);
lean_dec_ref(v___y_833_);
v___y_767_ = v___y_825_;
v___y_768_ = v___y_826_;
v___y_769_ = v___y_828_;
v___y_770_ = v___y_830_;
v___y_771_ = v___x_839_;
goto v___jp_766_;
}
v___jp_840_:
{
lean_object* v_queryPart_850_; 
v_queryPart_850_ = l_Std_Http_URI_Query_formatOption(v___y_848_);
if (lean_obj_tag(v___y_841_) == 0)
{
lean_object* v___x_851_; 
v___x_851_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_825_ = v___y_842_;
v___y_826_ = v___y_843_;
v___y_827_ = v___y_844_;
v___y_828_ = v___y_846_;
v___y_829_ = v___y_845_;
v___y_830_ = v___y_847_;
v___y_831_ = v_queryPart_850_;
v___y_832_ = v___y_849_;
v___y_833_ = v___x_851_;
goto v___jp_824_;
}
else
{
lean_object* v_val_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v_val_852_ = lean_ctor_get(v___y_841_, 0);
lean_inc(v_val_852_);
lean_dec_ref_known(v___y_841_, 1);
v___x_853_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__16));
v___x_854_ = l_Std_Http_URI_EncodedFragment_encode(v_val_852_);
lean_dec(v_val_852_);
v___x_855_ = lean_string_from_utf8_unchecked(v___x_854_);
v___x_856_ = lean_string_append(v___x_853_, v___x_855_);
lean_dec_ref(v___x_855_);
v___y_825_ = v___y_842_;
v___y_826_ = v___y_843_;
v___y_827_ = v___y_844_;
v___y_828_ = v___y_846_;
v___y_829_ = v___y_845_;
v___y_830_ = v___y_847_;
v___y_831_ = v_queryPart_850_;
v___y_832_ = v___y_849_;
v___y_833_ = v___x_856_;
goto v___jp_824_;
}
}
v___jp_857_:
{
lean_object* v_segments_867_; uint8_t v_absolute_868_; lean_object* v___x_869_; lean_object* v___x_870_; size_t v_sz_871_; size_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v_result_875_; 
v_segments_867_ = lean_ctor_get(v___y_865_, 0);
lean_inc_ref(v_segments_867_);
v_absolute_868_ = lean_ctor_get_uint8(v___y_865_, sizeof(void*)*1);
lean_dec_ref(v___y_865_);
v___x_869_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_870_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_871_ = lean_array_size(v_segments_867_);
v___x_872_ = ((size_t)0ULL);
v___x_873_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_870_, v___f_733_, v_sz_871_, v___x_872_, v_segments_867_);
v___x_874_ = lean_array_to_list(v___x_873_);
v_result_875_ = l_String_intercalate(v___x_869_, v___x_874_);
if (v_absolute_868_ == 0)
{
v___y_841_ = v___y_858_;
v___y_842_ = v___y_859_;
v___y_843_ = v___y_860_;
v___y_844_ = v___y_861_;
v___y_845_ = v___y_866_;
v___y_846_ = v___y_862_;
v___y_847_ = v___y_863_;
v___y_848_ = v___y_864_;
v___y_849_ = v_result_875_;
goto v___jp_840_;
}
else
{
lean_object* v___x_876_; 
v___x_876_ = lean_string_append(v___x_869_, v_result_875_);
lean_dec_ref(v_result_875_);
v___y_841_ = v___y_858_;
v___y_842_ = v___y_859_;
v___y_843_ = v___y_860_;
v___y_844_ = v___y_861_;
v___y_845_ = v___y_866_;
v___y_846_ = v___y_862_;
v___y_847_ = v___y_863_;
v___y_848_ = v___y_864_;
v___y_849_ = v___x_876_;
goto v___jp_840_;
}
}
v___jp_877_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = lean_string_append(v___y_881_, v___y_884_);
lean_dec_ref(v___y_884_);
v___x_891_ = lean_string_append(v___x_890_, v___y_889_);
lean_dec_ref(v___y_889_);
lean_inc_ref(v___y_888_);
v___x_892_ = lean_string_append(v___y_888_, v___x_891_);
lean_dec_ref(v___x_891_);
v___y_858_ = v___y_878_;
v___y_859_ = v___y_879_;
v___y_860_ = v___y_880_;
v___y_861_ = v___y_882_;
v___y_862_ = v___y_883_;
v___y_863_ = v___y_885_;
v___y_864_ = v___y_886_;
v___y_865_ = v___y_887_;
v___y_866_ = v___x_892_;
goto v___jp_857_;
}
v___jp_893_:
{
switch(lean_obj_tag(v_port_901_))
{
case 0:
{
lean_object* v___x_906_; 
v___x_906_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_878_ = v___y_894_;
v___y_879_ = v___y_895_;
v___y_880_ = v___y_897_;
v___y_881_ = v___y_896_;
v___y_882_ = v___y_898_;
v___y_883_ = v___y_899_;
v___y_884_ = v___y_905_;
v___y_885_ = v___y_900_;
v___y_886_ = v___y_902_;
v___y_887_ = v___y_903_;
v___y_888_ = v___y_904_;
v___y_889_ = v___x_906_;
goto v___jp_877_;
}
case 1:
{
lean_object* v___x_907_; 
v___x_907_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_878_ = v___y_894_;
v___y_879_ = v___y_895_;
v___y_880_ = v___y_897_;
v___y_881_ = v___y_896_;
v___y_882_ = v___y_898_;
v___y_883_ = v___y_899_;
v___y_884_ = v___y_905_;
v___y_885_ = v___y_900_;
v___y_886_ = v___y_902_;
v___y_887_ = v___y_903_;
v___y_888_ = v___y_904_;
v___y_889_ = v___x_907_;
goto v___jp_877_;
}
default: 
{
uint16_t v_port_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_port_908_ = lean_ctor_get_uint16(v_port_901_, 0);
lean_dec_ref_known(v_port_901_, 0);
v___x_909_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_910_ = lean_uint16_to_nat(v_port_908_);
v___x_911_ = l_Nat_reprFast(v___x_910_);
v___x_912_ = lean_string_append(v___x_909_, v___x_911_);
lean_dec_ref(v___x_911_);
v___y_878_ = v___y_894_;
v___y_879_ = v___y_895_;
v___y_880_ = v___y_897_;
v___y_881_ = v___y_896_;
v___y_882_ = v___y_898_;
v___y_883_ = v___y_899_;
v___y_884_ = v___y_905_;
v___y_885_ = v___y_900_;
v___y_886_ = v___y_902_;
v___y_887_ = v___y_903_;
v___y_888_ = v___y_904_;
v___y_889_ = v___x_912_;
goto v___jp_877_;
}
}
}
v___jp_913_:
{
switch(lean_obj_tag(v_host_920_))
{
case 0:
{
lean_object* v_name_926_; 
v_name_926_ = lean_ctor_get(v_host_920_, 0);
lean_inc_ref(v_name_926_);
lean_dec_ref_known(v_host_920_, 1);
v___y_894_ = v___y_914_;
v___y_895_ = v___y_915_;
v___y_896_ = v___y_925_;
v___y_897_ = v___y_916_;
v___y_898_ = v___y_917_;
v___y_899_ = v___y_918_;
v___y_900_ = v___y_919_;
v_port_901_ = v_port_921_;
v___y_902_ = v___y_922_;
v___y_903_ = v___y_923_;
v___y_904_ = v___y_924_;
v___y_905_ = v_name_926_;
goto v___jp_893_;
}
case 1:
{
lean_object* v_ipv4_927_; lean_object* v___x_928_; 
v_ipv4_927_ = lean_ctor_get(v_host_920_, 0);
lean_inc_ref(v_ipv4_927_);
lean_dec_ref_known(v_host_920_, 1);
v___x_928_ = lean_uv_ntop_v4(v_ipv4_927_);
lean_dec_ref(v_ipv4_927_);
v___y_894_ = v___y_914_;
v___y_895_ = v___y_915_;
v___y_896_ = v___y_925_;
v___y_897_ = v___y_916_;
v___y_898_ = v___y_917_;
v___y_899_ = v___y_918_;
v___y_900_ = v___y_919_;
v_port_901_ = v_port_921_;
v___y_902_ = v___y_922_;
v___y_903_ = v___y_923_;
v___y_904_ = v___y_924_;
v___y_905_ = v___x_928_;
goto v___jp_893_;
}
default: 
{
lean_object* v_ipv6_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_ipv6_929_ = lean_ctor_get(v_host_920_, 0);
lean_inc_ref(v_ipv6_929_);
lean_dec_ref_known(v_host_920_, 1);
v___x_930_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_931_ = lean_uv_ntop_v6(v_ipv6_929_);
lean_dec_ref(v_ipv6_929_);
v___x_932_ = lean_string_append(v___x_930_, v___x_931_);
lean_dec_ref(v___x_931_);
v___x_933_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_934_ = lean_string_append(v___x_932_, v___x_933_);
v___y_894_ = v___y_914_;
v___y_895_ = v___y_915_;
v___y_896_ = v___y_925_;
v___y_897_ = v___y_916_;
v___y_898_ = v___y_917_;
v___y_899_ = v___y_918_;
v___y_900_ = v___y_919_;
v_port_901_ = v_port_921_;
v___y_902_ = v___y_922_;
v___y_903_ = v___y_923_;
v___y_904_ = v___y_924_;
v___y_905_ = v___x_934_;
goto v___jp_893_;
}
}
}
v___jp_935_:
{
lean_object* v_queryStr_942_; lean_object* v___x_943_; 
v_queryStr_942_ = l_Std_Http_URI_Query_formatOption(v___y_940_);
v___x_943_ = lean_string_append(v___y_941_, v_queryStr_942_);
lean_dec_ref(v_queryStr_942_);
v___y_767_ = v___y_936_;
v___y_768_ = v___y_937_;
v___y_769_ = v___y_938_;
v___y_770_ = v___y_939_;
v___y_771_ = v___x_943_;
goto v___jp_766_;
}
v___jp_944_:
{
lean_object* v_data_946_; lean_object* v_size_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_data_946_ = lean_ctor_get(v_buffer_735_, 0);
lean_inc_ref(v_data_946_);
v_size_947_ = lean_ctor_get(v_buffer_735_, 1);
lean_inc(v_size_947_);
lean_dec_ref(v_buffer_735_);
v___x_948_ = lean_string_to_utf8(v___y_945_);
lean_inc_ref(v___x_948_);
v___x_949_ = lean_array_push(v_data_946_, v___x_948_);
v___x_950_ = lean_byte_array_size(v___x_948_);
lean_dec_ref(v___x_948_);
v___x_951_ = lean_nat_add(v_size_947_, v___x_950_);
lean_dec(v_size_947_);
v___x_952_ = ((lean_object*)(l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2));
v___x_953_ = lean_array_push(v___x_949_, v___x_952_);
v___x_954_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3);
v___x_955_ = lean_nat_add(v___x_951_, v___x_954_);
lean_dec(v___x_951_);
switch(lean_obj_tag(v_uri_739_))
{
case 0:
{
lean_object* v_path_956_; lean_object* v_query_957_; lean_object* v_segments_958_; uint8_t v_absolute_959_; lean_object* v___x_960_; lean_object* v___x_961_; size_t v_sz_962_; size_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_result_966_; 
lean_dec_ref(v___f_733_);
v_path_956_ = lean_ctor_get(v_uri_739_, 0);
lean_inc_ref(v_path_956_);
v_query_957_ = lean_ctor_get(v_uri_739_, 1);
lean_inc(v_query_957_);
lean_dec_ref_known(v_uri_739_, 2);
v_segments_958_ = lean_ctor_get(v_path_956_, 0);
lean_inc_ref(v_segments_958_);
v_absolute_959_ = lean_ctor_get_uint8(v_path_956_, sizeof(void*)*1);
lean_dec_ref(v_path_956_);
v___x_960_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_961_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_962_ = lean_array_size(v_segments_958_);
v___x_963_ = ((size_t)0ULL);
v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_961_, v___f_734_, v_sz_962_, v___x_963_, v_segments_958_);
v___x_965_ = lean_array_to_list(v___x_964_);
v_result_966_ = l_String_intercalate(v___x_960_, v___x_965_);
if (v_absolute_959_ == 0)
{
v___y_936_ = v___x_953_;
v___y_937_ = v___x_952_;
v___y_938_ = v___x_955_;
v___y_939_ = v___x_954_;
v___y_940_ = v_query_957_;
v___y_941_ = v_result_966_;
goto v___jp_935_;
}
else
{
lean_object* v___x_967_; 
v___x_967_ = lean_string_append(v___x_960_, v_result_966_);
lean_dec_ref(v_result_966_);
v___y_936_ = v___x_953_;
v___y_937_ = v___x_952_;
v___y_938_ = v___x_955_;
v___y_939_ = v___x_954_;
v___y_940_ = v_query_957_;
v___y_941_ = v___x_967_;
goto v___jp_935_;
}
}
case 1:
{
lean_object* v_uri_968_; lean_object* v_authority_969_; 
lean_dec_ref(v___f_734_);
v_uri_968_ = lean_ctor_get(v_uri_739_, 0);
lean_inc_ref(v_uri_968_);
lean_dec_ref_known(v_uri_739_, 1);
v_authority_969_ = lean_ctor_get(v_uri_968_, 1);
if (lean_obj_tag(v_authority_969_) == 0)
{
lean_object* v_scheme_970_; lean_object* v_path_971_; lean_object* v_query_972_; lean_object* v_fragment_973_; lean_object* v___x_974_; 
v_scheme_970_ = lean_ctor_get(v_uri_968_, 0);
lean_inc_ref(v_scheme_970_);
v_path_971_ = lean_ctor_get(v_uri_968_, 2);
lean_inc_ref(v_path_971_);
v_query_972_ = lean_ctor_get(v_uri_968_, 3);
lean_inc(v_query_972_);
v_fragment_973_ = lean_ctor_get(v_uri_968_, 4);
lean_inc(v_fragment_973_);
lean_dec_ref(v_uri_968_);
v___x_974_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_858_ = v_fragment_973_;
v___y_859_ = v___x_953_;
v___y_860_ = v___x_952_;
v___y_861_ = v_scheme_970_;
v___y_862_ = v___x_955_;
v___y_863_ = v___x_954_;
v___y_864_ = v_query_972_;
v___y_865_ = v_path_971_;
v___y_866_ = v___x_974_;
goto v___jp_857_;
}
else
{
lean_object* v_val_975_; lean_object* v_scheme_976_; lean_object* v_path_977_; lean_object* v_query_978_; lean_object* v_fragment_979_; lean_object* v_userInfo_980_; lean_object* v_host_981_; lean_object* v_port_982_; lean_object* v___x_983_; 
v_val_975_ = lean_ctor_get(v_authority_969_, 0);
lean_inc(v_val_975_);
v_scheme_976_ = lean_ctor_get(v_uri_968_, 0);
lean_inc_ref(v_scheme_976_);
v_path_977_ = lean_ctor_get(v_uri_968_, 2);
lean_inc_ref(v_path_977_);
v_query_978_ = lean_ctor_get(v_uri_968_, 3);
lean_inc(v_query_978_);
v_fragment_979_ = lean_ctor_get(v_uri_968_, 4);
lean_inc(v_fragment_979_);
lean_dec_ref(v_uri_968_);
v_userInfo_980_ = lean_ctor_get(v_val_975_, 0);
lean_inc(v_userInfo_980_);
v_host_981_ = lean_ctor_get(v_val_975_, 1);
lean_inc_ref(v_host_981_);
v_port_982_ = lean_ctor_get(v_val_975_, 2);
lean_inc(v_port_982_);
lean_dec(v_val_975_);
v___x_983_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__21));
if (lean_obj_tag(v_userInfo_980_) == 0)
{
lean_object* v___x_984_; 
v___x_984_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_914_ = v_fragment_979_;
v___y_915_ = v___x_953_;
v___y_916_ = v___x_952_;
v___y_917_ = v_scheme_976_;
v___y_918_ = v___x_955_;
v___y_919_ = v___x_954_;
v_host_920_ = v_host_981_;
v_port_921_ = v_port_982_;
v___y_922_ = v_query_978_;
v___y_923_ = v_path_977_;
v___y_924_ = v___x_983_;
v___y_925_ = v___x_984_;
goto v___jp_913_;
}
else
{
lean_object* v_val_985_; lean_object* v_password_986_; 
v_val_985_ = lean_ctor_get(v_userInfo_980_, 0);
lean_inc(v_val_985_);
lean_dec_ref_known(v_userInfo_980_, 1);
v_password_986_ = lean_ctor_get(v_val_985_, 1);
if (lean_obj_tag(v_password_986_) == 0)
{
lean_object* v_username_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_username_987_ = lean_ctor_get(v_val_985_, 0);
lean_inc_ref(v_username_987_);
lean_dec(v_val_985_);
v___x_988_ = lean_string_from_utf8_unchecked(v_username_987_);
v___x_989_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_990_ = lean_string_append(v___x_988_, v___x_989_);
v___y_914_ = v_fragment_979_;
v___y_915_ = v___x_953_;
v___y_916_ = v___x_952_;
v___y_917_ = v_scheme_976_;
v___y_918_ = v___x_955_;
v___y_919_ = v___x_954_;
v_host_920_ = v_host_981_;
v_port_921_ = v_port_982_;
v___y_922_ = v_query_978_;
v___y_923_ = v_path_977_;
v___y_924_ = v___x_983_;
v___y_925_ = v___x_990_;
goto v___jp_913_;
}
else
{
lean_object* v_username_991_; lean_object* v_val_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
lean_inc_ref(v_password_986_);
v_username_991_ = lean_ctor_get(v_val_985_, 0);
lean_inc_ref(v_username_991_);
lean_dec(v_val_985_);
v_val_992_ = lean_ctor_get(v_password_986_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v_password_986_, 1);
v___x_993_ = lean_string_from_utf8_unchecked(v_username_991_);
v___x_994_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_995_ = lean_string_append(v___x_993_, v___x_994_);
v___x_996_ = lean_string_from_utf8_unchecked(v_val_992_);
v___x_997_ = lean_string_append(v___x_995_, v___x_996_);
lean_dec_ref(v___x_996_);
v___x_998_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_999_ = lean_string_append(v___x_997_, v___x_998_);
v___y_914_ = v_fragment_979_;
v___y_915_ = v___x_953_;
v___y_916_ = v___x_952_;
v___y_917_ = v_scheme_976_;
v___y_918_ = v___x_955_;
v___y_919_ = v___x_954_;
v_host_920_ = v_host_981_;
v_port_921_ = v_port_982_;
v___y_922_ = v_query_978_;
v___y_923_ = v_path_977_;
v___y_924_ = v___x_983_;
v___y_925_ = v___x_999_;
goto v___jp_913_;
}
}
}
}
case 2:
{
lean_object* v_authority_1000_; lean_object* v_userInfo_1001_; 
lean_dec_ref(v___f_734_);
lean_dec_ref(v___f_733_);
v_authority_1000_ = lean_ctor_get(v_uri_739_, 0);
lean_inc_ref(v_authority_1000_);
lean_dec_ref_known(v_uri_739_, 1);
v_userInfo_1001_ = lean_ctor_get(v_authority_1000_, 0);
if (lean_obj_tag(v_userInfo_1001_) == 0)
{
lean_object* v_host_1002_; lean_object* v_port_1003_; lean_object* v___x_1004_; 
v_host_1002_ = lean_ctor_get(v_authority_1000_, 1);
lean_inc_ref(v_host_1002_);
v_port_1003_ = lean_ctor_get(v_authority_1000_, 2);
lean_inc(v_port_1003_);
lean_dec_ref(v_authority_1000_);
v___x_1004_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_808_ = v___x_953_;
v_host_809_ = v_host_1002_;
v_port_810_ = v_port_1003_;
v___y_811_ = v___x_952_;
v___y_812_ = v___x_955_;
v___y_813_ = v___x_954_;
v___y_814_ = v___x_1004_;
goto v___jp_807_;
}
else
{
lean_object* v_val_1005_; lean_object* v_password_1006_; 
v_val_1005_ = lean_ctor_get(v_userInfo_1001_, 0);
lean_inc(v_val_1005_);
v_password_1006_ = lean_ctor_get(v_val_1005_, 1);
if (lean_obj_tag(v_password_1006_) == 0)
{
lean_object* v_host_1007_; lean_object* v_port_1008_; lean_object* v_username_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_host_1007_ = lean_ctor_get(v_authority_1000_, 1);
lean_inc_ref(v_host_1007_);
v_port_1008_ = lean_ctor_get(v_authority_1000_, 2);
lean_inc(v_port_1008_);
lean_dec_ref(v_authority_1000_);
v_username_1009_ = lean_ctor_get(v_val_1005_, 0);
lean_inc_ref(v_username_1009_);
lean_dec(v_val_1005_);
v___x_1010_ = lean_string_from_utf8_unchecked(v_username_1009_);
v___x_1011_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_1012_ = lean_string_append(v___x_1010_, v___x_1011_);
v___y_808_ = v___x_953_;
v_host_809_ = v_host_1007_;
v_port_810_ = v_port_1008_;
v___y_811_ = v___x_952_;
v___y_812_ = v___x_955_;
v___y_813_ = v___x_954_;
v___y_814_ = v___x_1012_;
goto v___jp_807_;
}
else
{
lean_object* v_host_1013_; lean_object* v_port_1014_; lean_object* v_username_1015_; lean_object* v_val_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_inc_ref(v_password_1006_);
v_host_1013_ = lean_ctor_get(v_authority_1000_, 1);
lean_inc_ref(v_host_1013_);
v_port_1014_ = lean_ctor_get(v_authority_1000_, 2);
lean_inc(v_port_1014_);
lean_dec_ref(v_authority_1000_);
v_username_1015_ = lean_ctor_get(v_val_1005_, 0);
lean_inc_ref(v_username_1015_);
lean_dec(v_val_1005_);
v_val_1016_ = lean_ctor_get(v_password_1006_, 0);
lean_inc(v_val_1016_);
lean_dec_ref_known(v_password_1006_, 1);
v___x_1017_ = lean_string_from_utf8_unchecked(v_username_1015_);
v___x_1018_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_1019_ = lean_string_append(v___x_1017_, v___x_1018_);
v___x_1020_ = lean_string_from_utf8_unchecked(v_val_1016_);
v___x_1021_ = lean_string_append(v___x_1019_, v___x_1020_);
lean_dec_ref(v___x_1020_);
v___x_1022_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_1023_ = lean_string_append(v___x_1021_, v___x_1022_);
v___y_808_ = v___x_953_;
v_host_809_ = v_host_1013_;
v_port_810_ = v_port_1014_;
v___y_811_ = v___x_952_;
v___y_812_ = v___x_955_;
v___y_813_ = v___x_954_;
v___y_814_ = v___x_1023_;
goto v___jp_807_;
}
}
}
default: 
{
lean_object* v___x_1024_; 
lean_dec_ref(v___f_734_);
lean_dec_ref(v___f_733_);
v___x_1024_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__23));
v___y_767_ = v___x_953_;
v___y_768_ = v___x_952_;
v___y_769_ = v___x_955_;
v___y_770_ = v___x_954_;
v___y_771_ = v___x_1024_;
goto v___jp_766_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__0(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; uint8_t v___x_1073_; lean_object* v___x_1074_; 
v___x_1070_ = l_Std_Http_Headers_empty;
v___x_1071_ = lean_box(3);
v___x_1072_ = 1;
v___x_1073_ = 8;
v___x_1074_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1074_, 0, v___x_1071_);
lean_ctor_set(v___x_1074_, 1, v___x_1070_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*2, v___x_1073_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*2 + 1, v___x_1072_);
return v___x_1074_;
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__1(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1075_ = l_Std_Http_Extensions_empty;
v___x_1076_ = lean_obj_once(&l_Std_Http_Request_new___closed__0, &l_Std_Http_Request_new___closed__0_once, _init_l_Std_Http_Request_new___closed__0);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___x_1075_);
return v___x_1077_;
}
}
static lean_object* _init_l_Std_Http_Request_new(void){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_obj_once(&l_Std_Http_Request_new___closed__1, &l_Std_Http_Request_new___closed__1_once, _init_l_Std_Http_Request_new___closed__1);
return v___x_1078_;
}
}
lean_object* l_Std_Http_Request_Builder_method(lean_object* v_builder_1079_, uint8_t v_method_1080_){
_start:
{
lean_object* v_line_1081_; lean_object* v_extensions_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1099_; 
v_line_1081_ = lean_ctor_get(v_builder_1079_, 0);
v_extensions_1082_ = lean_ctor_get(v_builder_1079_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_builder_1079_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1084_ = v_builder_1079_;
v_isShared_1085_ = v_isSharedCheck_1099_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_extensions_1082_);
lean_inc(v_line_1081_);
lean_dec(v_builder_1079_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1099_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
uint8_t v_version_1086_; lean_object* v_uri_1087_; lean_object* v_headers_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1098_; 
v_version_1086_ = lean_ctor_get_uint8(v_line_1081_, sizeof(void*)*2 + 1);
v_uri_1087_ = lean_ctor_get(v_line_1081_, 0);
v_headers_1088_ = lean_ctor_get(v_line_1081_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_line_1081_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1090_ = v_line_1081_;
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_headers_1088_);
lean_inc(v_uri_1087_);
lean_dec(v_line_1081_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_uri_1087_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_headers_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1097_, sizeof(void*)*2 + 1, v_version_1086_);
v___x_1093_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1095_; 
lean_ctor_set_uint8(v___x_1093_, sizeof(void*)*2, v_method_1080_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1093_);
v___x_1095_ = v___x_1084_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_extensions_1082_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Request_Builder_method_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_1079_ = stack[0].m_obj;
uint8_t v_method_1080_ = stack[1].m_num;
lean_object* v_res_1100_;
v_res_1100_ = l_Std_Http_Request_Builder_method(v_builder_1079_, v_method_1080_);
stack->m_obj
 = v_res_1100_;
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method___boxed(lean_object* v_builder_1101_, lean_object* v_method_1102_){
_start:
{
uint8_t v_method_boxed_1103_; lean_object* v_res_1104_; 
v_method_boxed_1103_ = lean_unbox(v_method_1102_);
v_res_1104_ = l_Std_Http_Request_Builder_method(v_builder_1101_, v_method_boxed_1103_);
return v_res_1104_;
}
}
lean_object* l_Std_Http_Request_Builder_version(lean_object* v_builder_1105_, uint8_t v_version_1106_){
_start:
{
lean_object* v_line_1107_; lean_object* v_extensions_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1125_; 
v_line_1107_ = lean_ctor_get(v_builder_1105_, 0);
v_extensions_1108_ = lean_ctor_get(v_builder_1105_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_builder_1105_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1110_ = v_builder_1105_;
v_isShared_1111_ = v_isSharedCheck_1125_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_extensions_1108_);
lean_inc(v_line_1107_);
lean_dec(v_builder_1105_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1125_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
uint8_t v_method_1112_; lean_object* v_uri_1113_; lean_object* v_headers_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1124_; 
v_method_1112_ = lean_ctor_get_uint8(v_line_1107_, sizeof(void*)*2);
v_uri_1113_ = lean_ctor_get(v_line_1107_, 0);
v_headers_1114_ = lean_ctor_get(v_line_1107_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_line_1107_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1116_ = v_line_1107_;
v_isShared_1117_ = v_isSharedCheck_1124_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_headers_1114_);
lean_inc(v_uri_1113_);
lean_dec(v_line_1107_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1124_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_uri_1113_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_headers_1114_);
lean_ctor_set_uint8(v_reuseFailAlloc_1123_, sizeof(void*)*2, v_method_1112_);
v___x_1119_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*2 + 1, v_version_1106_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1119_);
v___x_1121_ = v___x_1110_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_extensions_1108_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Request_Builder_version_0interp(lean_interpreter_value* stack)
{
lean_object* v_builder_1105_ = stack[0].m_obj;
uint8_t v_version_1106_ = stack[1].m_num;
lean_object* v_res_1126_;
v_res_1126_ = l_Std_Http_Request_Builder_version(v_builder_1105_, v_version_1106_);
stack->m_obj
 = v_res_1126_;
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
v_array_1163_ = lean_ctor_get(v_pos_1162_, 0);
v_idx_1164_ = lean_ctor_get(v_pos_1162_, 1);
v___x_1165_ = lean_byte_array_size(v_array_1163_);
v___x_1166_ = lean_nat_dec_lt(v_idx_1164_, v___x_1165_);
if (v___x_1166_ == 0)
{
return v___x_1161_;
}
else
{
lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1174_; 
lean_inc(v_pos_1162_);
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(lean_object* v_a_1291_, lean_object* v_x_1292_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1291_ = stack[0].m_obj;
lean_object* v_x_1292_ = stack[1].m_obj;
uint8_t v_res_1298_;
v_res_1298_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1291_, v_x_1292_);
stack->m_num = v_res_1298_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg___boxed(lean_object* v_a_1299_, lean_object* v_x_1300_){
_start:
{
uint8_t v_res_1301_; lean_object* v_r_1302_; 
v_res_1301_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1299_, v_x_1300_);
lean_dec(v_x_1300_);
lean_dec_ref(v_a_1299_);
v_r_1302_ = lean_box(v_res_1301_);
return v_r_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1303_, lean_object* v_x_1304_){
_start:
{
if (lean_obj_tag(v_x_1304_) == 0)
{
return v_x_1303_;
}
else
{
lean_object* v_key_1305_; lean_object* v_value_1306_; lean_object* v_tail_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1330_; 
v_key_1305_ = lean_ctor_get(v_x_1304_, 0);
v_value_1306_ = lean_ctor_get(v_x_1304_, 1);
v_tail_1307_ = lean_ctor_get(v_x_1304_, 2);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_x_1304_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1309_ = v_x_1304_;
v_isShared_1310_ = v_isSharedCheck_1330_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_tail_1307_);
lean_inc(v_value_1306_);
lean_inc(v_key_1305_);
lean_dec(v_x_1304_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1330_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; uint64_t v___x_1312_; uint64_t v___x_1313_; uint64_t v___x_1314_; uint64_t v_fold_1315_; uint64_t v___x_1316_; uint64_t v___x_1317_; uint64_t v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1311_ = lean_array_get_size(v_x_1303_);
v___x_1312_ = lean_string_hash(v_key_1305_);
v___x_1313_ = 32ULL;
v___x_1314_ = lean_uint64_shift_right(v___x_1312_, v___x_1313_);
v_fold_1315_ = lean_uint64_xor(v___x_1312_, v___x_1314_);
v___x_1316_ = 16ULL;
v___x_1317_ = lean_uint64_shift_right(v_fold_1315_, v___x_1316_);
v___x_1318_ = lean_uint64_xor(v_fold_1315_, v___x_1317_);
v___x_1319_ = lean_uint64_to_usize(v___x_1318_);
v___x_1320_ = lean_usize_of_nat(v___x_1311_);
v___x_1321_ = ((size_t)1ULL);
v___x_1322_ = lean_usize_sub(v___x_1320_, v___x_1321_);
v___x_1323_ = lean_usize_land(v___x_1319_, v___x_1322_);
v___x_1324_ = lean_array_uget_borrowed(v_x_1303_, v___x_1323_);
lean_inc(v___x_1324_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 2, v___x_1324_);
v___x_1326_ = v___x_1309_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_key_1305_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_value_1306_);
lean_ctor_set(v_reuseFailAlloc_1329_, 2, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_array_uset(v_x_1303_, v___x_1323_, v___x_1326_);
v_x_1303_ = v___x_1327_;
v_x_1304_ = v_tail_1307_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1331_, lean_object* v_source_1332_, lean_object* v_target_1333_){
_start:
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = lean_array_get_size(v_source_1332_);
v___x_1335_ = lean_nat_dec_lt(v_i_1331_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_dec_ref(v_source_1332_);
lean_dec(v_i_1331_);
return v_target_1333_;
}
else
{
lean_object* v_es_1336_; lean_object* v___x_1337_; lean_object* v_source_1338_; lean_object* v_target_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_es_1336_ = lean_array_fget(v_source_1332_, v_i_1331_);
v___x_1337_ = lean_box(0);
v_source_1338_ = lean_array_fset(v_source_1332_, v_i_1331_, v___x_1337_);
v_target_1339_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1333_, v_es_1336_);
v___x_1340_ = lean_unsigned_to_nat(1u);
v___x_1341_ = lean_nat_add(v_i_1331_, v___x_1340_);
lean_dec(v_i_1331_);
v_i_1331_ = v___x_1341_;
v_source_1332_ = v_source_1338_;
v_target_1333_ = v_target_1339_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(lean_object* v_data_1343_){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v_nbuckets_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1344_ = lean_array_get_size(v_data_1343_);
v___x_1345_ = lean_unsigned_to_nat(2u);
v_nbuckets_1346_ = lean_nat_mul(v___x_1344_, v___x_1345_);
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = lean_box(0);
v___x_1349_ = lean_mk_array(v_nbuckets_1346_, v___x_1348_);
v___x_1350_ = lean_array_propagate_mark(v_data_1343_, v___x_1349_);
v___x_1351_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v___x_1347_, v_data_1343_, v___x_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(lean_object* v_i_1352_, lean_object* v_m_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_size_1355_; lean_object* v_buckets_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1406_; 
v_size_1355_ = lean_ctor_get(v_m_1353_, 0);
v_buckets_1356_ = lean_ctor_get(v_m_1353_, 1);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_m_1353_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1358_ = v_m_1353_;
v_isShared_1359_ = v_isSharedCheck_1406_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_buckets_1356_);
lean_inc(v_size_1355_);
lean_dec(v_m_1353_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1406_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; uint64_t v___x_1361_; uint64_t v___x_1362_; uint64_t v___x_1363_; uint64_t v_fold_1364_; uint64_t v___x_1365_; uint64_t v___x_1366_; uint64_t v___x_1367_; size_t v___x_1368_; size_t v___x_1369_; size_t v___x_1370_; size_t v___x_1371_; size_t v___x_1372_; lean_object* v_bkt_1373_; uint8_t v___x_1374_; 
v___x_1360_ = lean_array_get_size(v_buckets_1356_);
v___x_1361_ = lean_string_hash(v_a_1354_);
v___x_1362_ = 32ULL;
v___x_1363_ = lean_uint64_shift_right(v___x_1361_, v___x_1362_);
v_fold_1364_ = lean_uint64_xor(v___x_1361_, v___x_1363_);
v___x_1365_ = 16ULL;
v___x_1366_ = lean_uint64_shift_right(v_fold_1364_, v___x_1365_);
v___x_1367_ = lean_uint64_xor(v_fold_1364_, v___x_1366_);
v___x_1368_ = lean_uint64_to_usize(v___x_1367_);
v___x_1369_ = lean_usize_of_nat(v___x_1360_);
v___x_1370_ = ((size_t)1ULL);
v___x_1371_ = lean_usize_sub(v___x_1369_, v___x_1370_);
v___x_1372_ = lean_usize_land(v___x_1368_, v___x_1371_);
v_bkt_1373_ = lean_array_uget_borrowed(v_buckets_1356_, v___x_1372_);
v___x_1374_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1354_, v_bkt_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v_size_x27_1378_; lean_object* v___x_1379_; lean_object* v_buckets_x27_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1375_ = lean_unsigned_to_nat(1u);
v___x_1376_ = lean_mk_empty_array_with_capacity(v___x_1375_);
v___x_1377_ = lean_array_push(v___x_1376_, v_i_1352_);
v_size_x27_1378_ = lean_nat_add(v_size_1355_, v___x_1375_);
lean_dec(v_size_1355_);
lean_inc(v_bkt_1373_);
v___x_1379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1379_, 0, v_a_1354_);
lean_ctor_set(v___x_1379_, 1, v___x_1377_);
lean_ctor_set(v___x_1379_, 2, v_bkt_1373_);
v_buckets_x27_1380_ = lean_array_uset(v_buckets_1356_, v___x_1372_, v___x_1379_);
v___x_1381_ = lean_unsigned_to_nat(4u);
v___x_1382_ = lean_nat_mul(v_size_x27_1378_, v___x_1381_);
v___x_1383_ = lean_unsigned_to_nat(3u);
v___x_1384_ = lean_nat_div(v___x_1382_, v___x_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_array_get_size(v_buckets_x27_1380_);
v___x_1386_ = lean_nat_dec_le(v___x_1384_, v___x_1385_);
lean_dec(v___x_1384_);
if (v___x_1386_ == 0)
{
lean_object* v_val_1387_; lean_object* v___x_1389_; 
v_val_1387_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_buckets_x27_1380_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v_val_1387_);
lean_ctor_set(v___x_1358_, 0, v_size_x27_1378_);
v___x_1389_ = v___x_1358_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_size_x27_1378_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_val_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
else
{
lean_object* v___x_1392_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v_buckets_x27_1380_);
lean_ctor_set(v___x_1358_, 0, v_size_x27_1378_);
v___x_1392_ = v___x_1358_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_size_x27_1378_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_buckets_x27_1380_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
else
{
lean_object* v___x_1394_; lean_object* v_buckets_x27_1395_; lean_object* v_bkt_x27_1396_; lean_object* v___y_1398_; uint8_t v___x_1403_; 
lean_inc(v_bkt_1373_);
v___x_1394_ = lean_box(0);
v_buckets_x27_1395_ = lean_array_uset(v_buckets_1356_, v___x_1372_, v___x_1394_);
lean_inc_ref(v_a_1354_);
v_bkt_x27_1396_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_1352_, v_a_1354_, v_bkt_1373_);
v___x_1403_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1354_, v_bkt_x27_1396_);
lean_dec_ref(v_a_1354_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_unsigned_to_nat(1u);
v___x_1405_ = lean_nat_sub(v_size_1355_, v___x_1404_);
lean_dec(v_size_1355_);
v___y_1398_ = v___x_1405_;
goto v___jp_1397_;
}
else
{
v___y_1398_ = v_size_1355_;
goto v___jp_1397_;
}
v___jp_1397_:
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1399_ = lean_array_uset(v_buckets_x27_1395_, v___x_1372_, v_bkt_x27_1396_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v___x_1399_);
lean_ctor_set(v___x_1358_, 0, v___y_1398_);
v___x_1401_ = v___x_1358_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___y_1398_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header(lean_object* v_builder_1407_, lean_object* v_key_1408_, lean_object* v_value_1409_){
_start:
{
lean_object* v_line_1410_; lean_object* v_headers_1411_; lean_object* v_extensions_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1443_; 
v_line_1410_ = lean_ctor_get(v_builder_1407_, 0);
lean_inc_ref(v_line_1410_);
v_headers_1411_ = lean_ctor_get(v_line_1410_, 1);
lean_inc_ref(v_headers_1411_);
v_extensions_1412_ = lean_ctor_get(v_builder_1407_, 1);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_builder_1407_);
if (v_isSharedCheck_1443_ == 0)
{
lean_object* v_unused_1444_; 
v_unused_1444_ = lean_ctor_get(v_builder_1407_, 0);
lean_dec(v_unused_1444_);
v___x_1414_ = v_builder_1407_;
v_isShared_1415_ = v_isSharedCheck_1443_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_extensions_1412_);
lean_dec(v_builder_1407_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1443_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
uint8_t v_method_1416_; uint8_t v_version_1417_; lean_object* v_uri_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1441_; 
v_method_1416_ = lean_ctor_get_uint8(v_line_1410_, sizeof(void*)*2);
v_version_1417_ = lean_ctor_get_uint8(v_line_1410_, sizeof(void*)*2 + 1);
v_uri_1418_ = lean_ctor_get(v_line_1410_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_line_1410_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; 
v_unused_1442_ = lean_ctor_get(v_line_1410_, 1);
lean_dec(v_unused_1442_);
v___x_1420_ = v_line_1410_;
v_isShared_1421_ = v_isSharedCheck_1441_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_uri_1418_);
lean_dec(v_line_1410_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1441_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v_entries_1422_; lean_object* v_indexes_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1440_; 
v_entries_1422_ = lean_ctor_get(v_headers_1411_, 0);
v_indexes_1423_ = lean_ctor_get(v_headers_1411_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_headers_1411_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1425_ = v_headers_1411_;
v_isShared_1426_ = v_isSharedCheck_1440_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_indexes_1423_);
lean_inc(v_entries_1422_);
lean_dec(v_headers_1411_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1440_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v_i_1427_; lean_object* v___x_1428_; lean_object* v_entries_1429_; lean_object* v_indexes_1430_; lean_object* v___x_1432_; 
v_i_1427_ = lean_array_get_size(v_entries_1422_);
lean_inc_ref(v_key_1408_);
v___x_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1428_, 0, v_key_1408_);
lean_ctor_set(v___x_1428_, 1, v_value_1409_);
v_entries_1429_ = lean_array_push(v_entries_1422_, v___x_1428_);
v_indexes_1430_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1427_, v_indexes_1423_, v_key_1408_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 1, v_indexes_1430_);
lean_ctor_set(v___x_1425_, 0, v_entries_1429_);
v___x_1432_ = v___x_1425_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_entries_1429_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_indexes_1430_);
v___x_1432_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1434_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 1, v___x_1432_);
v___x_1434_ = v___x_1420_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_uri_1418_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v___x_1432_);
lean_ctor_set_uint8(v_reuseFailAlloc_1438_, sizeof(void*)*2, v_method_1416_);
lean_ctor_set_uint8(v_reuseFailAlloc_1438_, sizeof(void*)*2 + 1, v_version_1417_);
v___x_1434_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1434_);
v___x_1436_ = v___x_1414_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_extensions_1412_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(lean_object* v_00_u03b2_1445_, lean_object* v_a_1446_, lean_object* v_x_1447_){
_start:
{
uint8_t v___x_1448_; 
v___x_1448_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1446_, v_x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1446_ = stack[1].m_obj;
lean_object* v_x_1447_ = stack[2].m_obj;
uint8_t v_res_1449_;
v_res_1449_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(lean_box(0), v_a_1446_, v_x_1447_);
stack->m_num = v_res_1449_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1450_, lean_object* v_a_1451_, lean_object* v_x_1452_){
_start:
{
uint8_t v_res_1453_; lean_object* v_r_1454_; 
v_res_1453_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(v_00_u03b2_1450_, v_a_1451_, v_x_1452_);
lean_dec(v_x_1452_);
lean_dec_ref(v_a_1451_);
v_r_1454_ = lean_box(v_res_1453_);
return v_r_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1(lean_object* v_00_u03b2_1455_, lean_object* v_data_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_data_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1458_, lean_object* v_i_1459_, lean_object* v_source_1460_, lean_object* v_target_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v_i_1459_, v_source_1460_, v_target_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1463_, lean_object* v_x_1464_, lean_object* v_x_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1464_, v_x_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x21(lean_object* v_builder_1467_, lean_object* v_key_1468_, lean_object* v_value_1469_){
_start:
{
lean_object* v_line_1470_; lean_object* v_headers_1471_; lean_object* v_extensions_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1505_; 
v_line_1470_ = lean_ctor_get(v_builder_1467_, 0);
lean_inc_ref(v_line_1470_);
v_headers_1471_ = lean_ctor_get(v_line_1470_, 1);
lean_inc_ref(v_headers_1471_);
v_extensions_1472_ = lean_ctor_get(v_builder_1467_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_builder_1467_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v_builder_1467_, 0);
lean_dec(v_unused_1506_);
v___x_1474_ = v_builder_1467_;
v_isShared_1475_ = v_isSharedCheck_1505_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_extensions_1472_);
lean_dec(v_builder_1467_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1505_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
uint8_t v_method_1476_; uint8_t v_version_1477_; lean_object* v_uri_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1503_; 
v_method_1476_ = lean_ctor_get_uint8(v_line_1470_, sizeof(void*)*2);
v_version_1477_ = lean_ctor_get_uint8(v_line_1470_, sizeof(void*)*2 + 1);
v_uri_1478_ = lean_ctor_get(v_line_1470_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_line_1470_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; 
v_unused_1504_ = lean_ctor_get(v_line_1470_, 1);
lean_dec(v_unused_1504_);
v___x_1480_ = v_line_1470_;
v_isShared_1481_ = v_isSharedCheck_1503_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_uri_1478_);
lean_dec(v_line_1470_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1503_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v_entries_1482_; lean_object* v_indexes_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1502_; 
v_entries_1482_ = lean_ctor_get(v_headers_1471_, 0);
v_indexes_1483_ = lean_ctor_get(v_headers_1471_, 1);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_headers_1471_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1485_ = v_headers_1471_;
v_isShared_1486_ = v_isSharedCheck_1502_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_indexes_1483_);
lean_inc(v_entries_1482_);
lean_dec(v_headers_1471_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1502_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v_key_1487_; lean_object* v_value_1488_; lean_object* v_i_1489_; lean_object* v___x_1490_; lean_object* v_entries_1491_; lean_object* v_indexes_1492_; lean_object* v___x_1494_; 
v_key_1487_ = l_Std_Http_Header_Name_ofString_x21(v_key_1468_);
v_value_1488_ = l_Std_Http_Header_Value_ofString_x21(v_value_1469_);
v_i_1489_ = lean_array_get_size(v_entries_1482_);
lean_inc_ref(v_key_1487_);
v___x_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1490_, 0, v_key_1487_);
lean_ctor_set(v___x_1490_, 1, v_value_1488_);
v_entries_1491_ = lean_array_push(v_entries_1482_, v___x_1490_);
v_indexes_1492_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1489_, v_indexes_1483_, v_key_1487_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 1, v_indexes_1492_);
lean_ctor_set(v___x_1485_, 0, v_entries_1491_);
v___x_1494_ = v___x_1485_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_entries_1491_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_indexes_1492_);
v___x_1494_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1496_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v___x_1494_);
v___x_1496_ = v___x_1480_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_uri_1478_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v___x_1494_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*2, v_method_1476_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*2 + 1, v_version_1477_);
v___x_1496_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 0, v___x_1496_);
v___x_1498_ = v___x_1474_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_extensions_1472_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x3f(lean_object* v_builder_1507_, lean_object* v_key_1508_, lean_object* v_value_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Std_Http_Header_Name_ofString_x3f(v_key_1508_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v___x_1511_; 
lean_dec_ref(v_value_1509_);
lean_dec_ref(v_builder_1507_);
v___x_1511_ = lean_box(0);
return v___x_1511_;
}
else
{
lean_object* v_val_1512_; lean_object* v___x_1513_; 
v_val_1512_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_val_1512_);
lean_dec_ref_known(v___x_1510_, 1);
v___x_1513_ = l_Std_Http_Header_Value_ofString_x3f(v_value_1509_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v___x_1514_; 
lean_dec(v_val_1512_);
lean_dec_ref(v_builder_1507_);
v___x_1514_ = lean_box(0);
return v___x_1514_;
}
else
{
lean_object* v_line_1515_; lean_object* v_headers_1516_; lean_object* v_val_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1557_; 
v_line_1515_ = lean_ctor_get(v_builder_1507_, 0);
lean_inc_ref(v_line_1515_);
v_headers_1516_ = lean_ctor_get(v_line_1515_, 1);
lean_inc_ref(v_headers_1516_);
v_val_1517_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1519_ = v___x_1513_;
v_isShared_1520_ = v_isSharedCheck_1557_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_val_1517_);
lean_dec(v___x_1513_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1557_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v_extensions_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1555_; 
v_extensions_1521_ = lean_ctor_get(v_builder_1507_, 1);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_builder_1507_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; 
v_unused_1556_ = lean_ctor_get(v_builder_1507_, 0);
lean_dec(v_unused_1556_);
v___x_1523_ = v_builder_1507_;
v_isShared_1524_ = v_isSharedCheck_1555_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_extensions_1521_);
lean_dec(v_builder_1507_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1555_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
uint8_t v_method_1525_; uint8_t v_version_1526_; lean_object* v_uri_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1553_; 
v_method_1525_ = lean_ctor_get_uint8(v_line_1515_, sizeof(void*)*2);
v_version_1526_ = lean_ctor_get_uint8(v_line_1515_, sizeof(void*)*2 + 1);
v_uri_1527_ = lean_ctor_get(v_line_1515_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_line_1515_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; 
v_unused_1554_ = lean_ctor_get(v_line_1515_, 1);
lean_dec(v_unused_1554_);
v___x_1529_ = v_line_1515_;
v_isShared_1530_ = v_isSharedCheck_1553_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_uri_1527_);
lean_dec(v_line_1515_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1553_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v_entries_1531_; lean_object* v_indexes_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1552_; 
v_entries_1531_ = lean_ctor_get(v_headers_1516_, 0);
v_indexes_1532_ = lean_ctor_get(v_headers_1516_, 1);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_headers_1516_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1534_ = v_headers_1516_;
v_isShared_1535_ = v_isSharedCheck_1552_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_indexes_1532_);
lean_inc(v_entries_1531_);
lean_dec(v_headers_1516_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1552_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v_i_1536_; lean_object* v___x_1537_; lean_object* v_entries_1538_; lean_object* v_indexes_1539_; lean_object* v___x_1541_; 
v_i_1536_ = lean_array_get_size(v_entries_1531_);
lean_inc(v_val_1512_);
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_val_1512_);
lean_ctor_set(v___x_1537_, 1, v_val_1517_);
v_entries_1538_ = lean_array_push(v_entries_1531_, v___x_1537_);
v_indexes_1539_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1536_, v_indexes_1532_, v_val_1512_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 1, v_indexes_1539_);
lean_ctor_set(v___x_1534_, 0, v_entries_1538_);
v___x_1541_ = v___x_1534_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_entries_1538_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_indexes_1539_);
v___x_1541_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1543_; 
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 1, v___x_1541_);
v___x_1543_ = v___x_1529_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_uri_1527_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v___x_1541_);
lean_ctor_set_uint8(v_reuseFailAlloc_1550_, sizeof(void*)*2, v_method_1525_);
lean_ctor_set_uint8(v_reuseFailAlloc_1550_, sizeof(void*)*2 + 1, v_version_1526_);
v___x_1543_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1545_; 
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1543_);
v___x_1545_ = v___x_1523_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_extensions_1521_);
v___x_1545_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1547_; 
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1545_);
v___x_1547_ = v___x_1519_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
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
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headerOpt(lean_object* v_builder_1558_, lean_object* v_key_1559_, lean_object* v_value_1560_){
_start:
{
if (lean_obj_tag(v_value_1560_) == 0)
{
lean_dec_ref(v_key_1559_);
return v_builder_1558_;
}
else
{
lean_object* v_val_1561_; lean_object* v___x_1562_; 
v_val_1561_ = lean_ctor_get(v_value_1560_, 0);
lean_inc(v_val_1561_);
lean_dec_ref_known(v_value_1560_, 1);
v___x_1562_ = l_Std_Http_Request_Builder_header(v_builder_1558_, v_key_1559_, v_val_1561_);
return v___x_1562_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension___redArg(lean_object* v_builder_1564_, lean_object* v_inst_1565_, lean_object* v_data_1566_){
_start:
{
lean_object* v_line_1567_; lean_object* v_extensions_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1579_; 
v_line_1567_ = lean_ctor_get(v_builder_1564_, 0);
v_extensions_1568_ = lean_ctor_get(v_builder_1564_, 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_builder_1564_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1570_ = v_builder_1564_;
v_isShared_1571_ = v_isSharedCheck_1579_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_extensions_1568_);
lean_inc(v_line_1567_);
lean_dec(v_builder_1564_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1579_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v_dyn_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
v_dyn_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_1572_, 0, v_inst_1565_);
lean_ctor_set(v_dyn_1572_, 1, v_data_1566_);
v___x_1573_ = ((lean_object*)(l_Std_Http_Request_Builder_extension___redArg___closed__0));
v___x_1574_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_1572_);
v___x_1575_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1573_, v___x_1574_, v_dyn_1572_, v_extensions_1568_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 1, v___x_1575_);
v___x_1577_ = v___x_1570_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_line_1567_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension(lean_object* v_00_u03b1_1580_, lean_object* v_builder_1581_, lean_object* v_inst_1582_, lean_object* v_data_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Std_Http_Request_Builder_extension___redArg(v_builder_1581_, v_inst_1582_, v_data_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object* v_builder_1585_, lean_object* v_body_1586_){
_start:
{
lean_object* v_line_1587_; lean_object* v_extensions_1588_; lean_object* v___x_1589_; 
v_line_1587_ = lean_ctor_get(v_builder_1585_, 0);
v_extensions_1588_ = lean_ctor_get(v_builder_1585_, 1);
lean_inc(v_extensions_1588_);
lean_inc_ref(v_line_1587_);
v___x_1589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1589_, 0, v_line_1587_);
lean_ctor_set(v___x_1589_, 1, v_body_1586_);
lean_ctor_set(v___x_1589_, 2, v_extensions_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg___boxed(lean_object* v_builder_1590_, lean_object* v_body_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1590_, v_body_1591_);
lean_dec_ref(v_builder_1590_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body(lean_object* v_t_1593_, lean_object* v_builder_1594_, lean_object* v_body_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1594_, v_body_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___boxed(lean_object* v_t_1597_, lean_object* v_builder_1598_, lean_object* v_body_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Std_Http_Request_Builder_body(v_t_1597_, v_builder_1598_, v_body_1599_);
lean_dec_ref(v_builder_1598_);
return v_res_1600_;
}
}
static lean_object* _init_l_Std_Http_Request_get___closed__0(void){
_start:
{
uint8_t v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1601_ = 8;
v___x_1602_ = l_Std_Http_Request_new;
v___x_1603_ = l_Std_Http_Request_Builder_method(v___x_1602_, v___x_1601_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_get(lean_object* v_uri_1604_){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_obj_once(&l_Std_Http_Request_get___closed__0, &l_Std_Http_Request_get___closed__0_once, _init_l_Std_Http_Request_get___closed__0);
v___x_1606_ = l_Std_Http_Request_Builder_uri(v___x_1605_, v_uri_1604_);
return v___x_1606_;
}
}
static lean_object* _init_l_Std_Http_Request_post___closed__0(void){
_start:
{
uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1607_ = 23;
v___x_1608_ = l_Std_Http_Request_new;
v___x_1609_ = l_Std_Http_Request_Builder_method(v___x_1608_, v___x_1607_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_post(lean_object* v_uri_1610_){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_obj_once(&l_Std_Http_Request_post___closed__0, &l_Std_Http_Request_post___closed__0_once, _init_l_Std_Http_Request_post___closed__0);
v___x_1612_ = l_Std_Http_Request_Builder_uri(v___x_1611_, v_uri_1610_);
return v___x_1612_;
}
}
static lean_object* _init_l_Std_Http_Request_put___closed__0(void){
_start:
{
uint8_t v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1613_ = 27;
v___x_1614_ = l_Std_Http_Request_new;
v___x_1615_ = l_Std_Http_Request_Builder_method(v___x_1614_, v___x_1613_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_put(lean_object* v_uri_1616_){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_obj_once(&l_Std_Http_Request_put___closed__0, &l_Std_Http_Request_put___closed__0_once, _init_l_Std_Http_Request_put___closed__0);
v___x_1618_ = l_Std_Http_Request_Builder_uri(v___x_1617_, v_uri_1616_);
return v___x_1618_;
}
}
static lean_object* _init_l_Std_Http_Request_delete___closed__0(void){
_start:
{
uint8_t v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1619_ = 7;
v___x_1620_ = l_Std_Http_Request_new;
v___x_1621_ = l_Std_Http_Request_Builder_method(v___x_1620_, v___x_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_delete(lean_object* v_uri_1622_){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_obj_once(&l_Std_Http_Request_delete___closed__0, &l_Std_Http_Request_delete___closed__0_once, _init_l_Std_Http_Request_delete___closed__0);
v___x_1624_ = l_Std_Http_Request_Builder_uri(v___x_1623_, v_uri_1622_);
return v___x_1624_;
}
}
static lean_object* _init_l_Std_Http_Request_patch___closed__0(void){
_start:
{
uint8_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1625_ = 22;
v___x_1626_ = l_Std_Http_Request_new;
v___x_1627_ = l_Std_Http_Request_Builder_method(v___x_1626_, v___x_1625_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_patch(lean_object* v_uri_1628_){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_obj_once(&l_Std_Http_Request_patch___closed__0, &l_Std_Http_Request_patch___closed__0_once, _init_l_Std_Http_Request_patch___closed__0);
v___x_1630_ = l_Std_Http_Request_Builder_uri(v___x_1629_, v_uri_1628_);
return v___x_1630_;
}
}
static lean_object* _init_l_Std_Http_Request_head___closed__0(void){
_start:
{
uint8_t v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = 9;
v___x_1632_ = l_Std_Http_Request_new;
v___x_1633_ = l_Std_Http_Request_Builder_method(v___x_1632_, v___x_1631_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_head(lean_object* v_uri_1634_){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = lean_obj_once(&l_Std_Http_Request_head___closed__0, &l_Std_Http_Request_head___closed__0_once, _init_l_Std_Http_Request_head___closed__0);
v___x_1636_ = l_Std_Http_Request_Builder_uri(v___x_1635_, v_uri_1634_);
return v___x_1636_;
}
}
static lean_object* _init_l_Std_Http_Request_options___closed__0(void){
_start:
{
uint8_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1637_ = 20;
v___x_1638_ = l_Std_Http_Request_new;
v___x_1639_ = l_Std_Http_Request_Builder_method(v___x_1638_, v___x_1637_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_options(lean_object* v_uri_1640_){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = lean_obj_once(&l_Std_Http_Request_options___closed__0, &l_Std_Http_Request_options___closed__0_once, _init_l_Std_Http_Request_options___closed__0);
v___x_1642_ = l_Std_Http_Request_Builder_uri(v___x_1641_, v_uri_1640_);
return v___x_1642_;
}
}
static lean_object* _init_l_Std_Http_Request_connect___closed__0(void){
_start:
{
uint8_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1643_ = 5;
v___x_1644_ = l_Std_Http_Request_new;
v___x_1645_ = l_Std_Http_Request_Builder_method(v___x_1644_, v___x_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_connect(lean_object* v_uri_1646_){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_obj_once(&l_Std_Http_Request_connect___closed__0, &l_Std_Http_Request_connect___closed__0_once, _init_l_Std_Http_Request_connect___closed__0);
v___x_1648_ = l_Std_Http_Request_Builder_uri(v___x_1647_, v_uri_1646_);
return v___x_1648_;
}
}
static lean_object* _init_l_Std_Http_Request_trace___closed__0(void){
_start:
{
uint8_t v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = 32;
v___x_1650_ = l_Std_Http_Request_new;
v___x_1651_ = l_Std_Http_Request_Builder_method(v___x_1650_, v___x_1649_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_trace(lean_object* v_uri_1652_){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_obj_once(&l_Std_Http_Request_trace___closed__0, &l_Std_Http_Request_trace___closed__0_once, _init_l_Std_Http_Request_trace___closed__0);
v___x_1654_ = l_Std_Http_Request_Builder_uri(v___x_1653_, v_uri_1652_);
return v___x_1654_;
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
