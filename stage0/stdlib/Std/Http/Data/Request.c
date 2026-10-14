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
uint8_t v_method_308_; uint8_t v_version_309_; lean_object* v_uri_310_; lean_object* v_headers_311_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v_port_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v_host_430_; lean_object* v_port_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v_port_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v_host_465_; lean_object* v_port_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_480_; 
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
lean_object* v___x_552_; 
v___x_552_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__24));
v___y_480_ = v___x_552_;
goto v___jp_479_;
}
case 1:
{
lean_object* v___x_553_; 
v___x_553_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__25));
v___y_480_ = v___x_553_;
goto v___jp_479_;
}
case 2:
{
lean_object* v___x_554_; 
v___x_554_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__26));
v___y_480_ = v___x_554_;
goto v___jp_479_;
}
case 3:
{
lean_object* v___x_555_; 
v___x_555_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__27));
v___y_480_ = v___x_555_;
goto v___jp_479_;
}
case 4:
{
lean_object* v___x_556_; 
v___x_556_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__28));
v___y_480_ = v___x_556_;
goto v___jp_479_;
}
case 5:
{
lean_object* v___x_557_; 
v___x_557_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__29));
v___y_480_ = v___x_557_;
goto v___jp_479_;
}
case 6:
{
lean_object* v___x_558_; 
v___x_558_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__30));
v___y_480_ = v___x_558_;
goto v___jp_479_;
}
case 7:
{
lean_object* v___x_559_; 
v___x_559_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__31));
v___y_480_ = v___x_559_;
goto v___jp_479_;
}
case 8:
{
lean_object* v___x_560_; 
v___x_560_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__32));
v___y_480_ = v___x_560_;
goto v___jp_479_;
}
case 9:
{
lean_object* v___x_561_; 
v___x_561_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__33));
v___y_480_ = v___x_561_;
goto v___jp_479_;
}
case 10:
{
lean_object* v___x_562_; 
v___x_562_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__34));
v___y_480_ = v___x_562_;
goto v___jp_479_;
}
case 11:
{
lean_object* v___x_563_; 
v___x_563_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__35));
v___y_480_ = v___x_563_;
goto v___jp_479_;
}
case 12:
{
lean_object* v___x_564_; 
v___x_564_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__36));
v___y_480_ = v___x_564_;
goto v___jp_479_;
}
case 13:
{
lean_object* v___x_565_; 
v___x_565_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__37));
v___y_480_ = v___x_565_;
goto v___jp_479_;
}
case 14:
{
lean_object* v___x_566_; 
v___x_566_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__38));
v___y_480_ = v___x_566_;
goto v___jp_479_;
}
case 15:
{
lean_object* v___x_567_; 
v___x_567_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__39));
v___y_480_ = v___x_567_;
goto v___jp_479_;
}
case 16:
{
lean_object* v___x_568_; 
v___x_568_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__40));
v___y_480_ = v___x_568_;
goto v___jp_479_;
}
case 17:
{
lean_object* v___x_569_; 
v___x_569_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__41));
v___y_480_ = v___x_569_;
goto v___jp_479_;
}
case 18:
{
lean_object* v___x_570_; 
v___x_570_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__42));
v___y_480_ = v___x_570_;
goto v___jp_479_;
}
case 19:
{
lean_object* v___x_571_; 
v___x_571_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__43));
v___y_480_ = v___x_571_;
goto v___jp_479_;
}
case 20:
{
lean_object* v___x_572_; 
v___x_572_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__44));
v___y_480_ = v___x_572_;
goto v___jp_479_;
}
case 21:
{
lean_object* v___x_573_; 
v___x_573_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__45));
v___y_480_ = v___x_573_;
goto v___jp_479_;
}
case 22:
{
lean_object* v___x_574_; 
v___x_574_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__46));
v___y_480_ = v___x_574_;
goto v___jp_479_;
}
case 23:
{
lean_object* v___x_575_; 
v___x_575_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__47));
v___y_480_ = v___x_575_;
goto v___jp_479_;
}
case 24:
{
lean_object* v___x_576_; 
v___x_576_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__48));
v___y_480_ = v___x_576_;
goto v___jp_479_;
}
case 25:
{
lean_object* v___x_577_; 
v___x_577_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__49));
v___y_480_ = v___x_577_;
goto v___jp_479_;
}
case 26:
{
lean_object* v___x_578_; 
v___x_578_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__50));
v___y_480_ = v___x_578_;
goto v___jp_479_;
}
case 27:
{
lean_object* v___x_579_; 
v___x_579_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__51));
v___y_480_ = v___x_579_;
goto v___jp_479_;
}
case 28:
{
lean_object* v___x_580_; 
v___x_580_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__52));
v___y_480_ = v___x_580_;
goto v___jp_479_;
}
case 29:
{
lean_object* v___x_581_; 
v___x_581_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__53));
v___y_480_ = v___x_581_;
goto v___jp_479_;
}
case 30:
{
lean_object* v___x_582_; 
v___x_582_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__54));
v___y_480_ = v___x_582_;
goto v___jp_479_;
}
case 31:
{
lean_object* v___x_583_; 
v___x_583_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__55));
v___y_480_ = v___x_583_;
goto v___jp_479_;
}
case 32:
{
lean_object* v___x_584_; 
v___x_584_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__56));
v___y_480_ = v___x_584_;
goto v___jp_479_;
}
case 33:
{
lean_object* v___x_585_; 
v___x_585_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__57));
v___y_480_ = v___x_585_;
goto v___jp_479_;
}
case 34:
{
lean_object* v___x_586_; 
v___x_586_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__58));
v___y_480_ = v___x_586_;
goto v___jp_479_;
}
case 35:
{
lean_object* v___x_587_; 
v___x_587_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__59));
v___y_480_ = v___x_587_;
goto v___jp_479_;
}
case 36:
{
lean_object* v___x_588_; 
v___x_588_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__60));
v___y_480_ = v___x_588_;
goto v___jp_479_;
}
case 37:
{
lean_object* v___x_589_; 
v___x_589_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__61));
v___y_480_ = v___x_589_;
goto v___jp_479_;
}
case 38:
{
lean_object* v___x_590_; 
v___x_590_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__62));
v___y_480_ = v___x_590_;
goto v___jp_479_;
}
default: 
{
lean_object* v___x_591_; 
v___x_591_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__63));
v___y_480_ = v___x_591_;
goto v___jp_479_;
}
}
v___jp_312_:
{
lean_object* v_entries_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; size_t v_sz_320_; size_t v___x_321_; lean_object* v_pairs_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_entries_315_ = lean_ctor_get(v_headers_311_, 0);
lean_inc_ref(v_entries_315_);
lean_dec_ref(v_headers_311_);
v___x_316_ = lean_string_append(v___y_313_, v___y_314_);
v___x_317_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__0));
v___x_318_ = lean_string_append(v___x_316_, v___x_317_);
v___x_319_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_320_ = lean_array_size(v_entries_315_);
v___x_321_ = ((size_t)0ULL);
v_pairs_322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_319_, v___f_304_, v_sz_320_, v___x_321_, v_entries_315_);
v___x_323_ = lean_array_to_list(v_pairs_322_);
v___x_324_ = l_String_intercalate(v___x_317_, v___x_323_);
v___x_325_ = lean_string_append(v___x_318_, v___x_324_);
lean_dec_ref(v___x_324_);
v___x_326_ = lean_string_append(v___x_325_, v___x_317_);
return v___x_326_;
}
v___jp_327_:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_string_append(v___y_328_, v___y_330_);
lean_dec_ref(v___y_330_);
v___x_332_ = lean_string_append(v___x_331_, v___y_329_);
switch(v_version_309_)
{
case 0:
{
lean_object* v___x_333_; 
v___x_333_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__11));
v___y_313_ = v___x_332_;
v___y_314_ = v___x_333_;
goto v___jp_312_;
}
case 1:
{
lean_object* v___x_334_; 
v___x_334_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__12));
v___y_313_ = v___x_332_;
v___y_314_ = v___x_334_;
goto v___jp_312_;
}
case 2:
{
lean_object* v___x_335_; 
v___x_335_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__13));
v___y_313_ = v___x_332_;
v___y_314_ = v___x_335_;
goto v___jp_312_;
}
default: 
{
lean_object* v___x_336_; 
v___x_336_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__14));
v___y_313_ = v___x_332_;
v___y_314_ = v___x_336_;
goto v___jp_312_;
}
}
}
v___jp_337_:
{
lean_object* v_queryStr_342_; lean_object* v___x_343_; 
v_queryStr_342_ = l_Std_Http_URI_Query_formatOption(v___y_340_);
v___x_343_ = lean_string_append(v___y_341_, v_queryStr_342_);
lean_dec_ref(v_queryStr_342_);
v___y_328_ = v___y_338_;
v___y_329_ = v___y_339_;
v___y_330_ = v___x_343_;
goto v___jp_327_;
}
v___jp_344_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_352_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_353_ = lean_string_append(v___y_350_, v___x_352_);
v___x_354_ = lean_string_append(v___x_353_, v___y_348_);
lean_dec_ref(v___y_348_);
v___x_355_ = lean_string_append(v___x_354_, v___y_349_);
lean_dec_ref(v___y_349_);
v___x_356_ = lean_string_append(v___x_355_, v___y_347_);
lean_dec_ref(v___y_347_);
v___x_357_ = lean_string_append(v___x_356_, v___y_351_);
lean_dec_ref(v___y_351_);
v___y_328_ = v___y_345_;
v___y_329_ = v___y_346_;
v___y_330_ = v___x_357_;
goto v___jp_327_;
}
v___jp_358_:
{
lean_object* v_queryPart_366_; 
v_queryPart_366_ = l_Std_Http_URI_Query_formatOption(v___y_359_);
if (lean_obj_tag(v___y_362_) == 0)
{
lean_object* v___x_367_; 
v___x_367_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_345_ = v___y_360_;
v___y_346_ = v___y_361_;
v___y_347_ = v_queryPart_366_;
v___y_348_ = v___y_363_;
v___y_349_ = v___y_365_;
v___y_350_ = v___y_364_;
v___y_351_ = v___x_367_;
goto v___jp_344_;
}
else
{
lean_object* v_val_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_val_368_ = lean_ctor_get(v___y_362_, 0);
lean_inc(v_val_368_);
lean_dec_ref_known(v___y_362_, 1);
v___x_369_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__16));
v___x_370_ = l_Std_Http_URI_EncodedFragment_encode(v_val_368_);
lean_dec(v_val_368_);
v___x_371_ = lean_string_from_utf8_unchecked(v___x_370_);
v___x_372_ = lean_string_append(v___x_369_, v___x_371_);
lean_dec_ref(v___x_371_);
v___y_345_ = v___y_360_;
v___y_346_ = v___y_361_;
v___y_347_ = v_queryPart_366_;
v___y_348_ = v___y_363_;
v___y_349_ = v___y_365_;
v___y_350_ = v___y_364_;
v___y_351_ = v___x_372_;
goto v___jp_344_;
}
}
v___jp_373_:
{
lean_object* v_segments_381_; uint8_t v_absolute_382_; lean_object* v___x_383_; lean_object* v___x_384_; size_t v_sz_385_; size_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v_result_389_; 
v_segments_381_ = lean_ctor_get(v___y_378_, 0);
lean_inc_ref(v_segments_381_);
v_absolute_382_ = lean_ctor_get_uint8(v___y_378_, sizeof(void*)*1);
lean_dec_ref(v___y_378_);
v___x_383_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_384_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_385_ = lean_array_size(v_segments_381_);
v___x_386_ = ((size_t)0ULL);
v___x_387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_384_, v___f_305_, v_sz_385_, v___x_386_, v_segments_381_);
v___x_388_ = lean_array_to_list(v___x_387_);
v_result_389_ = l_String_intercalate(v___x_383_, v___x_388_);
if (v_absolute_382_ == 0)
{
v___y_359_ = v___y_374_;
v___y_360_ = v___y_375_;
v___y_361_ = v___y_376_;
v___y_362_ = v___y_377_;
v___y_363_ = v___y_380_;
v___y_364_ = v___y_379_;
v___y_365_ = v_result_389_;
goto v___jp_358_;
}
else
{
lean_object* v___x_390_; 
v___x_390_ = lean_string_append(v___x_383_, v_result_389_);
lean_dec_ref(v_result_389_);
v___y_359_ = v___y_374_;
v___y_360_ = v___y_375_;
v___y_361_ = v___y_376_;
v___y_362_ = v___y_377_;
v___y_363_ = v___y_380_;
v___y_364_ = v___y_379_;
v___y_365_ = v___x_390_;
goto v___jp_358_;
}
}
v___jp_391_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = lean_string_append(v___y_400_, v___y_398_);
lean_dec_ref(v___y_398_);
v___x_403_ = lean_string_append(v___x_402_, v___y_401_);
lean_dec_ref(v___y_401_);
lean_inc_ref(v___y_397_);
v___x_404_ = lean_string_append(v___y_397_, v___x_403_);
lean_dec_ref(v___x_403_);
v___y_374_ = v___y_392_;
v___y_375_ = v___y_393_;
v___y_376_ = v___y_394_;
v___y_377_ = v___y_395_;
v___y_378_ = v___y_396_;
v___y_379_ = v___y_399_;
v___y_380_ = v___x_404_;
goto v___jp_373_;
}
v___jp_405_:
{
switch(lean_obj_tag(v_port_412_))
{
case 0:
{
lean_object* v___x_416_; 
v___x_416_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_392_ = v___y_406_;
v___y_393_ = v___y_407_;
v___y_394_ = v___y_408_;
v___y_395_ = v___y_409_;
v___y_396_ = v___y_410_;
v___y_397_ = v___y_411_;
v___y_398_ = v___y_415_;
v___y_399_ = v___y_414_;
v___y_400_ = v___y_413_;
v___y_401_ = v___x_416_;
goto v___jp_391_;
}
case 1:
{
lean_object* v___x_417_; 
v___x_417_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_392_ = v___y_406_;
v___y_393_ = v___y_407_;
v___y_394_ = v___y_408_;
v___y_395_ = v___y_409_;
v___y_396_ = v___y_410_;
v___y_397_ = v___y_411_;
v___y_398_ = v___y_415_;
v___y_399_ = v___y_414_;
v___y_400_ = v___y_413_;
v___y_401_ = v___x_417_;
goto v___jp_391_;
}
default: 
{
uint16_t v_port_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v_port_418_ = lean_ctor_get_uint16(v_port_412_, 0);
lean_dec_ref_known(v_port_412_, 0);
v___x_419_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_420_ = lean_uint16_to_nat(v_port_418_);
v___x_421_ = l_Nat_reprFast(v___x_420_);
v___x_422_ = lean_string_append(v___x_419_, v___x_421_);
lean_dec_ref(v___x_421_);
v___y_392_ = v___y_406_;
v___y_393_ = v___y_407_;
v___y_394_ = v___y_408_;
v___y_395_ = v___y_409_;
v___y_396_ = v___y_410_;
v___y_397_ = v___y_411_;
v___y_398_ = v___y_415_;
v___y_399_ = v___y_414_;
v___y_400_ = v___y_413_;
v___y_401_ = v___x_422_;
goto v___jp_391_;
}
}
}
v___jp_423_:
{
switch(lean_obj_tag(v_host_430_))
{
case 0:
{
lean_object* v_name_434_; 
v_name_434_ = lean_ctor_get(v_host_430_, 0);
lean_inc_ref(v_name_434_);
lean_dec_ref_known(v_host_430_, 1);
v___y_406_ = v___y_424_;
v___y_407_ = v___y_425_;
v___y_408_ = v___y_426_;
v___y_409_ = v___y_427_;
v___y_410_ = v___y_428_;
v___y_411_ = v___y_429_;
v_port_412_ = v_port_431_;
v___y_413_ = v___y_433_;
v___y_414_ = v___y_432_;
v___y_415_ = v_name_434_;
goto v___jp_405_;
}
case 1:
{
lean_object* v_ipv4_435_; lean_object* v___x_436_; 
v_ipv4_435_ = lean_ctor_get(v_host_430_, 0);
lean_inc_ref(v_ipv4_435_);
lean_dec_ref_known(v_host_430_, 1);
v___x_436_ = lean_uv_ntop_v4(v_ipv4_435_);
lean_dec_ref(v_ipv4_435_);
v___y_406_ = v___y_424_;
v___y_407_ = v___y_425_;
v___y_408_ = v___y_426_;
v___y_409_ = v___y_427_;
v___y_410_ = v___y_428_;
v___y_411_ = v___y_429_;
v_port_412_ = v_port_431_;
v___y_413_ = v___y_433_;
v___y_414_ = v___y_432_;
v___y_415_ = v___x_436_;
goto v___jp_405_;
}
default: 
{
lean_object* v_ipv6_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_ipv6_437_ = lean_ctor_get(v_host_430_, 0);
lean_inc_ref(v_ipv6_437_);
lean_dec_ref_known(v_host_430_, 1);
v___x_438_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_439_ = lean_uv_ntop_v6(v_ipv6_437_);
lean_dec_ref(v_ipv6_437_);
v___x_440_ = lean_string_append(v___x_438_, v___x_439_);
lean_dec_ref(v___x_439_);
v___x_441_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_442_ = lean_string_append(v___x_440_, v___x_441_);
v___y_406_ = v___y_424_;
v___y_407_ = v___y_425_;
v___y_408_ = v___y_426_;
v___y_409_ = v___y_427_;
v___y_410_ = v___y_428_;
v___y_411_ = v___y_429_;
v_port_412_ = v_port_431_;
v___y_413_ = v___y_433_;
v___y_414_ = v___y_432_;
v___y_415_ = v___x_442_;
goto v___jp_405_;
}
}
}
v___jp_443_:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_string_append(v___y_446_, v___y_447_);
lean_dec_ref(v___y_447_);
v___x_450_ = lean_string_append(v___x_449_, v___y_448_);
lean_dec_ref(v___y_448_);
v___y_328_ = v___y_444_;
v___y_329_ = v___y_445_;
v___y_330_ = v___x_450_;
goto v___jp_327_;
}
v___jp_451_:
{
switch(lean_obj_tag(v_port_452_))
{
case 0:
{
lean_object* v___x_457_; 
v___x_457_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_444_ = v___y_453_;
v___y_445_ = v___y_454_;
v___y_446_ = v___y_455_;
v___y_447_ = v___y_456_;
v___y_448_ = v___x_457_;
goto v___jp_443_;
}
case 1:
{
lean_object* v___x_458_; 
v___x_458_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_444_ = v___y_453_;
v___y_445_ = v___y_454_;
v___y_446_ = v___y_455_;
v___y_447_ = v___y_456_;
v___y_448_ = v___x_458_;
goto v___jp_443_;
}
default: 
{
uint16_t v_port_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_port_459_ = lean_ctor_get_uint16(v_port_452_, 0);
lean_dec_ref_known(v_port_452_, 0);
v___x_460_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_461_ = lean_uint16_to_nat(v_port_459_);
v___x_462_ = l_Nat_reprFast(v___x_461_);
v___x_463_ = lean_string_append(v___x_460_, v___x_462_);
lean_dec_ref(v___x_462_);
v___y_444_ = v___y_453_;
v___y_445_ = v___y_454_;
v___y_446_ = v___y_455_;
v___y_447_ = v___y_456_;
v___y_448_ = v___x_463_;
goto v___jp_443_;
}
}
}
v___jp_464_:
{
switch(lean_obj_tag(v_host_465_))
{
case 0:
{
lean_object* v_name_470_; 
v_name_470_ = lean_ctor_get(v_host_465_, 0);
lean_inc_ref(v_name_470_);
lean_dec_ref_known(v_host_465_, 1);
v_port_452_ = v_port_466_;
v___y_453_ = v___y_467_;
v___y_454_ = v___y_468_;
v___y_455_ = v___y_469_;
v___y_456_ = v_name_470_;
goto v___jp_451_;
}
case 1:
{
lean_object* v_ipv4_471_; lean_object* v___x_472_; 
v_ipv4_471_ = lean_ctor_get(v_host_465_, 0);
lean_inc_ref(v_ipv4_471_);
lean_dec_ref_known(v_host_465_, 1);
v___x_472_ = lean_uv_ntop_v4(v_ipv4_471_);
lean_dec_ref(v_ipv4_471_);
v_port_452_ = v_port_466_;
v___y_453_ = v___y_467_;
v___y_454_ = v___y_468_;
v___y_455_ = v___y_469_;
v___y_456_ = v___x_472_;
goto v___jp_451_;
}
default: 
{
lean_object* v_ipv6_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_ipv6_473_ = lean_ctor_get(v_host_465_, 0);
lean_inc_ref(v_ipv6_473_);
lean_dec_ref_known(v_host_465_, 1);
v___x_474_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_475_ = lean_uv_ntop_v6(v_ipv6_473_);
lean_dec_ref(v_ipv6_473_);
v___x_476_ = lean_string_append(v___x_474_, v___x_475_);
lean_dec_ref(v___x_475_);
v___x_477_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_478_ = lean_string_append(v___x_476_, v___x_477_);
v_port_452_ = v_port_466_;
v___y_453_ = v___y_467_;
v___y_454_ = v___y_468_;
v___y_455_ = v___y_469_;
v___y_456_ = v___x_478_;
goto v___jp_451_;
}
}
}
v___jp_479_:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__20));
lean_inc_ref(v___y_480_);
v___x_482_ = lean_string_append(v___y_480_, v___x_481_);
switch(lean_obj_tag(v_uri_310_))
{
case 0:
{
lean_object* v_path_483_; lean_object* v_query_484_; lean_object* v_segments_485_; uint8_t v_absolute_486_; lean_object* v___x_487_; lean_object* v___x_488_; size_t v_sz_489_; size_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v_result_493_; 
lean_dec_ref(v___f_305_);
v_path_483_ = lean_ctor_get(v_uri_310_, 0);
lean_inc_ref(v_path_483_);
v_query_484_ = lean_ctor_get(v_uri_310_, 1);
lean_inc(v_query_484_);
lean_dec_ref_known(v_uri_310_, 2);
v_segments_485_ = lean_ctor_get(v_path_483_, 0);
lean_inc_ref(v_segments_485_);
v_absolute_486_ = lean_ctor_get_uint8(v_path_483_, sizeof(void*)*1);
lean_dec_ref(v_path_483_);
v___x_487_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_488_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_489_ = lean_array_size(v_segments_485_);
v___x_490_ = ((size_t)0ULL);
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_488_, v___f_306_, v_sz_489_, v___x_490_, v_segments_485_);
v___x_492_ = lean_array_to_list(v___x_491_);
v_result_493_ = l_String_intercalate(v___x_487_, v___x_492_);
if (v_absolute_486_ == 0)
{
v___y_338_ = v___x_482_;
v___y_339_ = v___x_481_;
v___y_340_ = v_query_484_;
v___y_341_ = v_result_493_;
goto v___jp_337_;
}
else
{
lean_object* v___x_494_; 
v___x_494_ = lean_string_append(v___x_487_, v_result_493_);
lean_dec_ref(v_result_493_);
v___y_338_ = v___x_482_;
v___y_339_ = v___x_481_;
v___y_340_ = v_query_484_;
v___y_341_ = v___x_494_;
goto v___jp_337_;
}
}
case 1:
{
lean_object* v_uri_495_; lean_object* v_authority_496_; 
lean_dec_ref(v___f_306_);
v_uri_495_ = lean_ctor_get(v_uri_310_, 0);
lean_inc_ref(v_uri_495_);
lean_dec_ref_known(v_uri_310_, 1);
v_authority_496_ = lean_ctor_get(v_uri_495_, 1);
if (lean_obj_tag(v_authority_496_) == 0)
{
lean_object* v_scheme_497_; lean_object* v_path_498_; lean_object* v_query_499_; lean_object* v_fragment_500_; lean_object* v___x_501_; 
v_scheme_497_ = lean_ctor_get(v_uri_495_, 0);
lean_inc_ref(v_scheme_497_);
v_path_498_ = lean_ctor_get(v_uri_495_, 2);
lean_inc_ref(v_path_498_);
v_query_499_ = lean_ctor_get(v_uri_495_, 3);
lean_inc(v_query_499_);
v_fragment_500_ = lean_ctor_get(v_uri_495_, 4);
lean_inc(v_fragment_500_);
lean_dec_ref(v_uri_495_);
v___x_501_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_374_ = v_query_499_;
v___y_375_ = v___x_482_;
v___y_376_ = v___x_481_;
v___y_377_ = v_fragment_500_;
v___y_378_ = v_path_498_;
v___y_379_ = v_scheme_497_;
v___y_380_ = v___x_501_;
goto v___jp_373_;
}
else
{
lean_object* v_val_502_; lean_object* v_scheme_503_; lean_object* v_path_504_; lean_object* v_query_505_; lean_object* v_fragment_506_; lean_object* v_userInfo_507_; lean_object* v_host_508_; lean_object* v_port_509_; lean_object* v___x_510_; 
v_val_502_ = lean_ctor_get(v_authority_496_, 0);
lean_inc(v_val_502_);
v_scheme_503_ = lean_ctor_get(v_uri_495_, 0);
lean_inc_ref(v_scheme_503_);
v_path_504_ = lean_ctor_get(v_uri_495_, 2);
lean_inc_ref(v_path_504_);
v_query_505_ = lean_ctor_get(v_uri_495_, 3);
lean_inc(v_query_505_);
v_fragment_506_ = lean_ctor_get(v_uri_495_, 4);
lean_inc(v_fragment_506_);
lean_dec_ref(v_uri_495_);
v_userInfo_507_ = lean_ctor_get(v_val_502_, 0);
lean_inc(v_userInfo_507_);
v_host_508_ = lean_ctor_get(v_val_502_, 1);
lean_inc_ref(v_host_508_);
v_port_509_ = lean_ctor_get(v_val_502_, 2);
lean_inc(v_port_509_);
lean_dec(v_val_502_);
v___x_510_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__21));
if (lean_obj_tag(v_userInfo_507_) == 0)
{
lean_object* v___x_511_; 
v___x_511_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_424_ = v_query_505_;
v___y_425_ = v___x_482_;
v___y_426_ = v___x_481_;
v___y_427_ = v_fragment_506_;
v___y_428_ = v_path_504_;
v___y_429_ = v___x_510_;
v_host_430_ = v_host_508_;
v_port_431_ = v_port_509_;
v___y_432_ = v_scheme_503_;
v___y_433_ = v___x_511_;
goto v___jp_423_;
}
else
{
lean_object* v_val_512_; lean_object* v_password_513_; 
v_val_512_ = lean_ctor_get(v_userInfo_507_, 0);
lean_inc(v_val_512_);
lean_dec_ref_known(v_userInfo_507_, 1);
v_password_513_ = lean_ctor_get(v_val_512_, 1);
if (lean_obj_tag(v_password_513_) == 0)
{
lean_object* v_username_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_username_514_ = lean_ctor_get(v_val_512_, 0);
lean_inc_ref(v_username_514_);
lean_dec(v_val_512_);
v___x_515_ = lean_string_from_utf8_unchecked(v_username_514_);
v___x_516_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_517_ = lean_string_append(v___x_515_, v___x_516_);
v___y_424_ = v_query_505_;
v___y_425_ = v___x_482_;
v___y_426_ = v___x_481_;
v___y_427_ = v_fragment_506_;
v___y_428_ = v_path_504_;
v___y_429_ = v___x_510_;
v_host_430_ = v_host_508_;
v_port_431_ = v_port_509_;
v___y_432_ = v_scheme_503_;
v___y_433_ = v___x_517_;
goto v___jp_423_;
}
else
{
lean_object* v_username_518_; lean_object* v_val_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
lean_inc_ref(v_password_513_);
v_username_518_ = lean_ctor_get(v_val_512_, 0);
lean_inc_ref(v_username_518_);
lean_dec(v_val_512_);
v_val_519_ = lean_ctor_get(v_password_513_, 0);
lean_inc(v_val_519_);
lean_dec_ref_known(v_password_513_, 1);
v___x_520_ = lean_string_from_utf8_unchecked(v_username_518_);
v___x_521_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_522_ = lean_string_append(v___x_520_, v___x_521_);
v___x_523_ = lean_string_from_utf8_unchecked(v_val_519_);
v___x_524_ = lean_string_append(v___x_522_, v___x_523_);
lean_dec_ref(v___x_523_);
v___x_525_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_526_ = lean_string_append(v___x_524_, v___x_525_);
v___y_424_ = v_query_505_;
v___y_425_ = v___x_482_;
v___y_426_ = v___x_481_;
v___y_427_ = v_fragment_506_;
v___y_428_ = v_path_504_;
v___y_429_ = v___x_510_;
v_host_430_ = v_host_508_;
v_port_431_ = v_port_509_;
v___y_432_ = v_scheme_503_;
v___y_433_ = v___x_526_;
goto v___jp_423_;
}
}
}
}
case 2:
{
lean_object* v_authority_527_; lean_object* v_userInfo_528_; 
lean_dec_ref(v___f_306_);
lean_dec_ref(v___f_305_);
v_authority_527_ = lean_ctor_get(v_uri_310_, 0);
lean_inc_ref(v_authority_527_);
lean_dec_ref_known(v_uri_310_, 1);
v_userInfo_528_ = lean_ctor_get(v_authority_527_, 0);
if (lean_obj_tag(v_userInfo_528_) == 0)
{
lean_object* v_host_529_; lean_object* v_port_530_; lean_object* v___x_531_; 
v_host_529_ = lean_ctor_get(v_authority_527_, 1);
lean_inc_ref(v_host_529_);
v_port_530_ = lean_ctor_get(v_authority_527_, 2);
lean_inc(v_port_530_);
lean_dec_ref(v_authority_527_);
v___x_531_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v_host_465_ = v_host_529_;
v_port_466_ = v_port_530_;
v___y_467_ = v___x_482_;
v___y_468_ = v___x_481_;
v___y_469_ = v___x_531_;
goto v___jp_464_;
}
else
{
lean_object* v_val_532_; lean_object* v_password_533_; 
v_val_532_ = lean_ctor_get(v_userInfo_528_, 0);
lean_inc(v_val_532_);
v_password_533_ = lean_ctor_get(v_val_532_, 1);
if (lean_obj_tag(v_password_533_) == 0)
{
lean_object* v_host_534_; lean_object* v_port_535_; lean_object* v_username_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_host_534_ = lean_ctor_get(v_authority_527_, 1);
lean_inc_ref(v_host_534_);
v_port_535_ = lean_ctor_get(v_authority_527_, 2);
lean_inc(v_port_535_);
lean_dec_ref(v_authority_527_);
v_username_536_ = lean_ctor_get(v_val_532_, 0);
lean_inc_ref(v_username_536_);
lean_dec(v_val_532_);
v___x_537_ = lean_string_from_utf8_unchecked(v_username_536_);
v___x_538_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_539_ = lean_string_append(v___x_537_, v___x_538_);
v_host_465_ = v_host_534_;
v_port_466_ = v_port_535_;
v___y_467_ = v___x_482_;
v___y_468_ = v___x_481_;
v___y_469_ = v___x_539_;
goto v___jp_464_;
}
else
{
lean_object* v_host_540_; lean_object* v_port_541_; lean_object* v_username_542_; lean_object* v_val_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
lean_inc_ref(v_password_533_);
v_host_540_ = lean_ctor_get(v_authority_527_, 1);
lean_inc_ref(v_host_540_);
v_port_541_ = lean_ctor_get(v_authority_527_, 2);
lean_inc(v_port_541_);
lean_dec_ref(v_authority_527_);
v_username_542_ = lean_ctor_get(v_val_532_, 0);
lean_inc_ref(v_username_542_);
lean_dec(v_val_532_);
v_val_543_ = lean_ctor_get(v_password_533_, 0);
lean_inc(v_val_543_);
lean_dec_ref_known(v_password_533_, 1);
v___x_544_ = lean_string_from_utf8_unchecked(v_username_542_);
v___x_545_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_546_ = lean_string_append(v___x_544_, v___x_545_);
v___x_547_ = lean_string_from_utf8_unchecked(v_val_543_);
v___x_548_ = lean_string_append(v___x_546_, v___x_547_);
lean_dec_ref(v___x_547_);
v___x_549_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_550_ = lean_string_append(v___x_548_, v___x_549_);
v_host_465_ = v_host_540_;
v_port_466_ = v_port_541_;
v___y_467_ = v___x_482_;
v___y_468_ = v___x_481_;
v___y_469_ = v___x_550_;
goto v___jp_464_;
}
}
}
default: 
{
lean_object* v___x_551_; 
lean_dec_ref(v___f_306_);
lean_dec_ref(v___f_305_);
v___x_551_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__23));
v___y_328_ = v___x_482_;
v___y_329_ = v___x_481_;
v___y_330_ = v___x_551_;
goto v___jp_327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1(lean_object* v___x_598_, lean_object* v___x_599_, lean_object* v___x_600_, lean_object* v_name_601_, lean_object* v___x_602_, uint32_t v___x_603_, lean_object* v___x_604_, lean_object* v_it_605_, lean_object* v_acc_606_, lean_object* v_hP_607_, lean_object* v_recur_608_){
_start:
{
lean_object* v_it_610_; lean_object* v_out_611_; lean_object* v_it_627_; lean_object* v_startInclusive_628_; lean_object* v_endExclusive_629_; 
if (lean_obj_tag(v_it_605_) == 0)
{
lean_object* v_currPos_641_; lean_object* v_searcher_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_664_; 
v_currPos_641_ = lean_ctor_get(v_it_605_, 0);
v_searcher_642_ = lean_ctor_get(v_it_605_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_it_605_);
if (v_isSharedCheck_664_ == 0)
{
v___x_644_ = v_it_605_;
v_isShared_645_ = v_isSharedCheck_664_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_searcher_642_);
lean_inc(v_currPos_641_);
lean_dec(v_it_605_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_664_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
uint8_t v_decide_646_; 
v_decide_646_ = lean_nat_dec_eq(v_searcher_642_, v___x_602_);
if (v_decide_646_ == 0)
{
uint32_t v___x_647_; uint8_t v___x_648_; 
lean_dec(v___x_602_);
v___x_647_ = lean_string_utf8_get_fast(v_name_601_, v_searcher_642_);
v___x_648_ = lean_uint32_dec_eq(v___x_647_, v___x_603_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = lean_string_utf8_next_fast(v_name_601_, v_searcher_642_);
lean_dec(v_searcher_642_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 1, v___x_649_);
v___x_651_ = v___x_644_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_currPos_641_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_649_);
v___x_651_ = v_reuseFailAlloc_653_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_652_; 
v___x_652_ = lean_apply_4(v_recur_608_, v___x_651_, v_acc_606_, lean_box(0), lean_box(0));
return v___x_652_;
}
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_slice_657_; lean_object* v_nextIt_659_; 
v___x_654_ = lean_string_utf8_next_fast(v_name_601_, v_searcher_642_);
v___x_655_ = lean_nat_sub(v___x_654_, v_searcher_642_);
v___x_656_ = lean_nat_add(v_searcher_642_, v___x_655_);
lean_dec(v___x_655_);
v_slice_657_ = l_String_Slice_subslice_x21(v___x_604_, v_currPos_641_, v_searcher_642_);
lean_inc(v___x_656_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 1, v___x_656_);
lean_ctor_set(v___x_644_, 0, v___x_656_);
v_nextIt_659_ = v___x_644_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v___x_656_);
v_nextIt_659_ = v_reuseFailAlloc_662_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v_startInclusive_660_; lean_object* v_endExclusive_661_; 
v_startInclusive_660_ = lean_ctor_get(v_slice_657_, 0);
lean_inc(v_startInclusive_660_);
v_endExclusive_661_ = lean_ctor_get(v_slice_657_, 1);
lean_inc(v_endExclusive_661_);
lean_dec_ref(v_slice_657_);
v_it_627_ = v_nextIt_659_;
v_startInclusive_628_ = v_startInclusive_660_;
v_endExclusive_629_ = v_endExclusive_661_;
goto v___jp_626_;
}
}
}
else
{
lean_object* v___x_663_; 
lean_del_object(v___x_644_);
lean_dec(v_searcher_642_);
v___x_663_ = lean_box(1);
v_it_627_ = v___x_663_;
v_startInclusive_628_ = v_currPos_641_;
v_endExclusive_629_ = v___x_602_;
goto v___jp_626_;
}
}
}
else
{
lean_dec_ref(v_recur_608_);
lean_dec(v___x_602_);
return v_acc_606_;
}
v___jp_609_:
{
if (lean_obj_tag(v_acc_606_) == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v_out_611_);
v___x_613_ = lean_apply_4(v_recur_608_, v_it_610_, v___x_612_, lean_box(0), lean_box(0));
return v___x_613_;
}
else
{
lean_object* v_val_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_625_; 
v_val_614_ = lean_ctor_get(v_acc_606_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v_acc_606_);
if (v_isSharedCheck_625_ == 0)
{
v___x_616_ = v_acc_606_;
v_isShared_617_ = v_isSharedCheck_625_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_val_614_);
lean_dec(v_acc_606_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_625_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_618_ = lean_string_utf8_extract_fast(v___x_598_, v___x_599_, v___x_600_);
v___x_619_ = lean_string_append(v_val_614_, v___x_618_);
lean_dec_ref(v___x_618_);
v___x_620_ = lean_string_append(v___x_619_, v_out_611_);
lean_dec_ref(v_out_611_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_620_);
v___x_622_ = v___x_616_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_624_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; 
v___x_623_ = lean_apply_4(v_recur_608_, v_it_610_, v___x_622_, lean_box(0), lean_box(0));
return v___x_623_;
}
}
}
}
v___jp_626_:
{
lean_object* v___x_630_; uint32_t v___x_631_; uint32_t v___x_632_; uint8_t v___x_633_; 
v___x_630_ = lean_string_utf8_extract_fast(v_name_601_, v_startInclusive_628_, v_endExclusive_629_);
lean_dec(v_endExclusive_629_);
lean_dec(v_startInclusive_628_);
v___x_631_ = lean_string_utf8_get(v___x_630_, v___x_599_);
v___x_632_ = 97;
v___x_633_ = lean_uint32_dec_le(v___x_632_, v___x_631_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
v___x_634_ = lean_string_utf8_set(v___x_630_, v___x_599_, v___x_631_);
v_it_610_ = v_it_627_;
v_out_611_ = v___x_634_;
goto v___jp_609_;
}
else
{
uint32_t v___x_635_; uint8_t v___x_636_; 
v___x_635_ = 122;
v___x_636_ = lean_uint32_dec_le(v___x_631_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
v___x_637_ = lean_string_utf8_set(v___x_630_, v___x_599_, v___x_631_);
v_it_610_ = v_it_627_;
v_out_611_ = v___x_637_;
goto v___jp_609_;
}
else
{
uint32_t v___x_638_; uint32_t v___x_639_; lean_object* v___x_640_; 
v___x_638_ = 4294967264;
v___x_639_ = lean_uint32_add(v___x_631_, v___x_638_);
v___x_640_ = lean_string_utf8_set(v___x_630_, v___x_599_, v___x_639_);
v_it_610_ = v_it_627_;
v_out_611_ = v___x_640_;
goto v___jp_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1___boxed(lean_object* v___x_665_, lean_object* v___x_666_, lean_object* v___x_667_, lean_object* v_name_668_, lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v___x_671_, lean_object* v_it_672_, lean_object* v_acc_673_, lean_object* v_hP_674_, lean_object* v_recur_675_){
_start:
{
uint32_t v___x_3057__boxed_676_; lean_object* v_res_677_; 
v___x_3057__boxed_676_ = lean_unbox_uint32(v___x_670_);
lean_dec(v___x_670_);
v_res_677_ = l_Std_Http_Request_instEncodeV11Head___lam__1(v___x_665_, v___x_666_, v___x_667_, v_name_668_, v___x_669_, v___x_3057__boxed_676_, v___x_671_, v_it_672_, v_acc_673_, v_hP_674_, v_recur_675_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v_name_668_);
lean_dec(v___x_667_);
lean_dec(v___x_666_);
lean_dec_ref(v___x_665_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0(lean_object* v_buf_678_, lean_object* v_name_679_, lean_object* v_value_680_){
_start:
{
lean_object* v___y_682_; lean_object* v___f_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_it_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___f_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___f_701_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__1));
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_string_utf8_byte_size(v_name_679_);
lean_inc_ref(v_name_679_);
v___x_704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_704_, 0, v_name_679_);
lean_ctor_set(v___x_704_, 1, v___x_702_);
lean_ctor_set(v___x_704_, 2, v___x_703_);
lean_inc_ref(v___x_704_);
v_it_705_ = l_String_Slice_splitToSubslice___redArg(v___x_704_, v___f_701_);
v___x_706_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__2));
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1;
v___f_709_ = lean_alloc_closure((void*)(l_Std_Http_Request_instEncodeV11Head___lam__1___boxed), 11, 7);
lean_closure_set(v___f_709_, 0, v___x_706_);
lean_closure_set(v___f_709_, 1, v___x_702_);
lean_closure_set(v___f_709_, 2, v___x_707_);
lean_closure_set(v___f_709_, 3, v_name_679_);
lean_closure_set(v___f_709_, 4, v___x_703_);
lean_closure_set(v___f_709_, 5, v___x_708_);
lean_closure_set(v___f_709_, 6, v___x_704_);
v___x_710_ = lean_box(0);
v___x_711_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_709_, v_it_705_, v___x_710_, lean_box(0));
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v___x_712_; 
v___x_712_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_682_ = v___x_712_;
goto v___jp_681_;
}
else
{
lean_object* v_val_713_; 
v_val_713_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_val_713_);
lean_dec_ref_known(v___x_711_, 1);
v___y_682_ = v_val_713_;
goto v___jp_681_;
}
v___jp_681_:
{
lean_object* v_data_683_; lean_object* v_size_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_700_; 
v_data_683_ = lean_ctor_get(v_buf_678_, 0);
v_size_684_ = lean_ctor_get(v_buf_678_, 1);
v_isSharedCheck_700_ = !lean_is_exclusive(v_buf_678_);
if (v_isSharedCheck_700_ == 0)
{
v___x_686_ = v_buf_678_;
v_isShared_687_ = v_isSharedCheck_700_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_size_684_);
lean_inc(v_data_683_);
lean_dec(v_buf_678_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_700_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_688_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__0));
v___x_689_ = lean_string_append(v___y_682_, v___x_688_);
v___x_690_ = lean_string_append(v___x_689_, v_value_680_);
v___x_691_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__0));
v___x_692_ = lean_string_append(v___x_690_, v___x_691_);
v___x_693_ = lean_string_to_utf8(v___x_692_);
lean_dec_ref(v___x_692_);
lean_inc_ref(v___x_693_);
v___x_694_ = lean_array_push(v_data_683_, v___x_693_);
v___x_695_ = lean_byte_array_size(v___x_693_);
lean_dec_ref(v___x_693_);
v___x_696_ = lean_nat_add(v_size_684_, v___x_695_);
lean_dec(v_size_684_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_696_);
lean_ctor_set(v___x_686_, 0, v___x_694_);
v___x_698_ = v___x_686_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___boxed(lean_object* v_buf_714_, lean_object* v_name_715_, lean_object* v_value_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Std_Http_Request_instEncodeV11Head___lam__0(v_buf_714_, v_name_715_, v_value_716_);
lean_dec_ref(v_value_716_);
return v_res_717_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__0));
v___x_719_ = lean_string_to_utf8(v___x_718_);
return v___x_719_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0);
v___x_721_ = lean_byte_array_size(v___x_720_);
return v___x_721_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = ((lean_object*)(l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2));
v___x_729_ = lean_byte_array_size(v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3(lean_object* v___f_730_, lean_object* v___f_731_, lean_object* v___f_732_, lean_object* v_buffer_733_, lean_object* v_req_734_){
_start:
{
uint8_t v_method_735_; uint8_t v_version_736_; lean_object* v_uri_737_; lean_object* v_headers_738_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v_port_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_806_; lean_object* v_host_807_; lean_object* v_port_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v_port_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v_host_918_; lean_object* v_port_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_943_; 
v_method_735_ = lean_ctor_get_uint8(v_req_734_, sizeof(void*)*2);
v_version_736_ = lean_ctor_get_uint8(v_req_734_, sizeof(void*)*2 + 1);
v_uri_737_ = lean_ctor_get(v_req_734_, 0);
lean_inc(v_uri_737_);
v_headers_738_ = lean_ctor_get(v_req_734_, 1);
lean_inc_ref(v_headers_738_);
lean_dec_ref(v_req_734_);
switch(v_method_735_)
{
case 0:
{
lean_object* v___x_1023_; 
v___x_1023_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__24));
v___y_943_ = v___x_1023_;
goto v___jp_942_;
}
case 1:
{
lean_object* v___x_1024_; 
v___x_1024_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__25));
v___y_943_ = v___x_1024_;
goto v___jp_942_;
}
case 2:
{
lean_object* v___x_1025_; 
v___x_1025_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__26));
v___y_943_ = v___x_1025_;
goto v___jp_942_;
}
case 3:
{
lean_object* v___x_1026_; 
v___x_1026_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__27));
v___y_943_ = v___x_1026_;
goto v___jp_942_;
}
case 4:
{
lean_object* v___x_1027_; 
v___x_1027_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__28));
v___y_943_ = v___x_1027_;
goto v___jp_942_;
}
case 5:
{
lean_object* v___x_1028_; 
v___x_1028_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__29));
v___y_943_ = v___x_1028_;
goto v___jp_942_;
}
case 6:
{
lean_object* v___x_1029_; 
v___x_1029_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__30));
v___y_943_ = v___x_1029_;
goto v___jp_942_;
}
case 7:
{
lean_object* v___x_1030_; 
v___x_1030_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__31));
v___y_943_ = v___x_1030_;
goto v___jp_942_;
}
case 8:
{
lean_object* v___x_1031_; 
v___x_1031_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__32));
v___y_943_ = v___x_1031_;
goto v___jp_942_;
}
case 9:
{
lean_object* v___x_1032_; 
v___x_1032_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__33));
v___y_943_ = v___x_1032_;
goto v___jp_942_;
}
case 10:
{
lean_object* v___x_1033_; 
v___x_1033_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__34));
v___y_943_ = v___x_1033_;
goto v___jp_942_;
}
case 11:
{
lean_object* v___x_1034_; 
v___x_1034_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__35));
v___y_943_ = v___x_1034_;
goto v___jp_942_;
}
case 12:
{
lean_object* v___x_1035_; 
v___x_1035_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__36));
v___y_943_ = v___x_1035_;
goto v___jp_942_;
}
case 13:
{
lean_object* v___x_1036_; 
v___x_1036_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__37));
v___y_943_ = v___x_1036_;
goto v___jp_942_;
}
case 14:
{
lean_object* v___x_1037_; 
v___x_1037_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__38));
v___y_943_ = v___x_1037_;
goto v___jp_942_;
}
case 15:
{
lean_object* v___x_1038_; 
v___x_1038_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__39));
v___y_943_ = v___x_1038_;
goto v___jp_942_;
}
case 16:
{
lean_object* v___x_1039_; 
v___x_1039_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__40));
v___y_943_ = v___x_1039_;
goto v___jp_942_;
}
case 17:
{
lean_object* v___x_1040_; 
v___x_1040_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__41));
v___y_943_ = v___x_1040_;
goto v___jp_942_;
}
case 18:
{
lean_object* v___x_1041_; 
v___x_1041_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__42));
v___y_943_ = v___x_1041_;
goto v___jp_942_;
}
case 19:
{
lean_object* v___x_1042_; 
v___x_1042_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__43));
v___y_943_ = v___x_1042_;
goto v___jp_942_;
}
case 20:
{
lean_object* v___x_1043_; 
v___x_1043_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__44));
v___y_943_ = v___x_1043_;
goto v___jp_942_;
}
case 21:
{
lean_object* v___x_1044_; 
v___x_1044_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__45));
v___y_943_ = v___x_1044_;
goto v___jp_942_;
}
case 22:
{
lean_object* v___x_1045_; 
v___x_1045_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__46));
v___y_943_ = v___x_1045_;
goto v___jp_942_;
}
case 23:
{
lean_object* v___x_1046_; 
v___x_1046_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__47));
v___y_943_ = v___x_1046_;
goto v___jp_942_;
}
case 24:
{
lean_object* v___x_1047_; 
v___x_1047_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__48));
v___y_943_ = v___x_1047_;
goto v___jp_942_;
}
case 25:
{
lean_object* v___x_1048_; 
v___x_1048_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__49));
v___y_943_ = v___x_1048_;
goto v___jp_942_;
}
case 26:
{
lean_object* v___x_1049_; 
v___x_1049_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__50));
v___y_943_ = v___x_1049_;
goto v___jp_942_;
}
case 27:
{
lean_object* v___x_1050_; 
v___x_1050_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__51));
v___y_943_ = v___x_1050_;
goto v___jp_942_;
}
case 28:
{
lean_object* v___x_1051_; 
v___x_1051_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__52));
v___y_943_ = v___x_1051_;
goto v___jp_942_;
}
case 29:
{
lean_object* v___x_1052_; 
v___x_1052_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__53));
v___y_943_ = v___x_1052_;
goto v___jp_942_;
}
case 30:
{
lean_object* v___x_1053_; 
v___x_1053_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__54));
v___y_943_ = v___x_1053_;
goto v___jp_942_;
}
case 31:
{
lean_object* v___x_1054_; 
v___x_1054_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__55));
v___y_943_ = v___x_1054_;
goto v___jp_942_;
}
case 32:
{
lean_object* v___x_1055_; 
v___x_1055_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__56));
v___y_943_ = v___x_1055_;
goto v___jp_942_;
}
case 33:
{
lean_object* v___x_1056_; 
v___x_1056_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__57));
v___y_943_ = v___x_1056_;
goto v___jp_942_;
}
case 34:
{
lean_object* v___x_1057_; 
v___x_1057_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__58));
v___y_943_ = v___x_1057_;
goto v___jp_942_;
}
case 35:
{
lean_object* v___x_1058_; 
v___x_1058_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__59));
v___y_943_ = v___x_1058_;
goto v___jp_942_;
}
case 36:
{
lean_object* v___x_1059_; 
v___x_1059_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__60));
v___y_943_ = v___x_1059_;
goto v___jp_942_;
}
case 37:
{
lean_object* v___x_1060_; 
v___x_1060_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__61));
v___y_943_ = v___x_1060_;
goto v___jp_942_;
}
case 38:
{
lean_object* v___x_1061_; 
v___x_1061_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__62));
v___y_943_ = v___x_1061_;
goto v___jp_942_;
}
default: 
{
lean_object* v___x_1062_; 
v___x_1062_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__63));
v___y_943_ = v___x_1062_;
goto v___jp_942_;
}
}
v___jp_739_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_buffer_751_; lean_object* v_buffer_752_; lean_object* v_data_753_; lean_object* v_size_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_763_; 
v___x_743_ = lean_string_to_utf8(v___y_742_);
lean_inc_ref(v___x_743_);
v___x_744_ = lean_array_push(v___y_741_, v___x_743_);
v___x_745_ = lean_byte_array_size(v___x_743_);
lean_dec_ref(v___x_743_);
v___x_746_ = lean_nat_add(v___y_740_, v___x_745_);
lean_dec(v___y_740_);
v___x_747_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0);
v___x_748_ = lean_array_push(v___x_744_, v___x_747_);
v___x_749_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1);
v___x_750_ = lean_nat_add(v___x_746_, v___x_749_);
lean_dec(v___x_746_);
v_buffer_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_751_, 0, v___x_748_);
lean_ctor_set(v_buffer_751_, 1, v___x_750_);
v_buffer_752_ = l_Std_Http_Headers_fold___redArg(v_headers_738_, v_buffer_751_, v___f_730_);
lean_dec_ref(v_headers_738_);
v_data_753_ = lean_ctor_get(v_buffer_752_, 0);
v_size_754_ = lean_ctor_get(v_buffer_752_, 1);
v_isSharedCheck_763_ = !lean_is_exclusive(v_buffer_752_);
if (v_isSharedCheck_763_ == 0)
{
v___x_756_ = v_buffer_752_;
v_isShared_757_ = v_isSharedCheck_763_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_size_754_);
lean_inc(v_data_753_);
lean_dec(v_buffer_752_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_763_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_758_ = lean_array_push(v_data_753_, v___x_747_);
v___x_759_ = lean_nat_add(v_size_754_, v___x_749_);
lean_dec(v_size_754_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 1, v___x_759_);
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_761_ = v___x_756_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
v___jp_764_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_770_ = lean_string_to_utf8(v___y_769_);
lean_dec_ref(v___y_769_);
lean_inc_ref(v___x_770_);
v___x_771_ = lean_array_push(v___y_765_, v___x_770_);
v___x_772_ = lean_byte_array_size(v___x_770_);
lean_dec_ref(v___x_770_);
v___x_773_ = lean_nat_add(v___y_767_, v___x_772_);
lean_dec(v___y_767_);
v___x_774_ = lean_array_push(v___x_771_, v___y_766_);
v___x_775_ = lean_nat_add(v___x_773_, v___y_768_);
lean_dec(v___x_773_);
switch(v_version_736_)
{
case 0:
{
lean_object* v___x_776_; 
v___x_776_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__11));
v___y_740_ = v___x_775_;
v___y_741_ = v___x_774_;
v___y_742_ = v___x_776_;
goto v___jp_739_;
}
case 1:
{
lean_object* v___x_777_; 
v___x_777_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__12));
v___y_740_ = v___x_775_;
v___y_741_ = v___x_774_;
v___y_742_ = v___x_777_;
goto v___jp_739_;
}
case 2:
{
lean_object* v___x_778_; 
v___x_778_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__13));
v___y_740_ = v___x_775_;
v___y_741_ = v___x_774_;
v___y_742_ = v___x_778_;
goto v___jp_739_;
}
default: 
{
lean_object* v___x_779_; 
v___x_779_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__14));
v___y_740_ = v___x_775_;
v___y_741_ = v___x_774_;
v___y_742_ = v___x_779_;
goto v___jp_739_;
}
}
}
v___jp_780_:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_string_append(v___y_783_, v___y_786_);
lean_dec_ref(v___y_786_);
v___x_789_ = lean_string_append(v___x_788_, v___y_787_);
lean_dec_ref(v___y_787_);
v___y_765_ = v___y_781_;
v___y_766_ = v___y_782_;
v___y_767_ = v___y_784_;
v___y_768_ = v___y_785_;
v___y_769_ = v___x_789_;
goto v___jp_764_;
}
v___jp_790_:
{
switch(lean_obj_tag(v_port_791_))
{
case 0:
{
lean_object* v___x_798_; 
v___x_798_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_781_ = v___y_792_;
v___y_782_ = v___y_794_;
v___y_783_ = v___y_793_;
v___y_784_ = v___y_795_;
v___y_785_ = v___y_796_;
v___y_786_ = v___y_797_;
v___y_787_ = v___x_798_;
goto v___jp_780_;
}
case 1:
{
lean_object* v___x_799_; 
v___x_799_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_781_ = v___y_792_;
v___y_782_ = v___y_794_;
v___y_783_ = v___y_793_;
v___y_784_ = v___y_795_;
v___y_785_ = v___y_796_;
v___y_786_ = v___y_797_;
v___y_787_ = v___x_799_;
goto v___jp_780_;
}
default: 
{
uint16_t v_port_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_port_800_ = lean_ctor_get_uint16(v_port_791_, 0);
lean_dec_ref_known(v_port_791_, 0);
v___x_801_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_802_ = lean_uint16_to_nat(v_port_800_);
v___x_803_ = l_Nat_reprFast(v___x_802_);
v___x_804_ = lean_string_append(v___x_801_, v___x_803_);
lean_dec_ref(v___x_803_);
v___y_781_ = v___y_792_;
v___y_782_ = v___y_794_;
v___y_783_ = v___y_793_;
v___y_784_ = v___y_795_;
v___y_785_ = v___y_796_;
v___y_786_ = v___y_797_;
v___y_787_ = v___x_804_;
goto v___jp_780_;
}
}
}
v___jp_805_:
{
switch(lean_obj_tag(v_host_807_))
{
case 0:
{
lean_object* v_name_813_; 
v_name_813_ = lean_ctor_get(v_host_807_, 0);
lean_inc_ref(v_name_813_);
lean_dec_ref_known(v_host_807_, 1);
v_port_791_ = v_port_808_;
v___y_792_ = v___y_806_;
v___y_793_ = v___y_812_;
v___y_794_ = v___y_809_;
v___y_795_ = v___y_810_;
v___y_796_ = v___y_811_;
v___y_797_ = v_name_813_;
goto v___jp_790_;
}
case 1:
{
lean_object* v_ipv4_814_; lean_object* v___x_815_; 
v_ipv4_814_ = lean_ctor_get(v_host_807_, 0);
lean_inc_ref(v_ipv4_814_);
lean_dec_ref_known(v_host_807_, 1);
v___x_815_ = lean_uv_ntop_v4(v_ipv4_814_);
lean_dec_ref(v_ipv4_814_);
v_port_791_ = v_port_808_;
v___y_792_ = v___y_806_;
v___y_793_ = v___y_812_;
v___y_794_ = v___y_809_;
v___y_795_ = v___y_810_;
v___y_796_ = v___y_811_;
v___y_797_ = v___x_815_;
goto v___jp_790_;
}
default: 
{
lean_object* v_ipv6_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_ipv6_816_ = lean_ctor_get(v_host_807_, 0);
lean_inc_ref(v_ipv6_816_);
lean_dec_ref_known(v_host_807_, 1);
v___x_817_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_818_ = lean_uv_ntop_v6(v_ipv6_816_);
lean_dec_ref(v_ipv6_816_);
v___x_819_ = lean_string_append(v___x_817_, v___x_818_);
lean_dec_ref(v___x_818_);
v___x_820_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_821_ = lean_string_append(v___x_819_, v___x_820_);
v_port_791_ = v_port_808_;
v___y_792_ = v___y_806_;
v___y_793_ = v___y_812_;
v___y_794_ = v___y_809_;
v___y_795_ = v___y_810_;
v___y_796_ = v___y_811_;
v___y_797_ = v___x_821_;
goto v___jp_790_;
}
}
}
v___jp_822_:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_832_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_833_ = lean_string_append(v___y_825_, v___x_832_);
v___x_834_ = lean_string_append(v___x_833_, v___y_827_);
lean_dec_ref(v___y_827_);
v___x_835_ = lean_string_append(v___x_834_, v___y_830_);
lean_dec_ref(v___y_830_);
v___x_836_ = lean_string_append(v___x_835_, v___y_829_);
lean_dec_ref(v___y_829_);
v___x_837_ = lean_string_append(v___x_836_, v___y_831_);
lean_dec_ref(v___y_831_);
v___y_765_ = v___y_823_;
v___y_766_ = v___y_824_;
v___y_767_ = v___y_826_;
v___y_768_ = v___y_828_;
v___y_769_ = v___x_837_;
goto v___jp_764_;
}
v___jp_838_:
{
lean_object* v_queryPart_848_; 
v_queryPart_848_ = l_Std_Http_URI_Query_formatOption(v___y_846_);
if (lean_obj_tag(v___y_839_) == 0)
{
lean_object* v___x_849_; 
v___x_849_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_823_ = v___y_840_;
v___y_824_ = v___y_841_;
v___y_825_ = v___y_842_;
v___y_826_ = v___y_844_;
v___y_827_ = v___y_843_;
v___y_828_ = v___y_845_;
v___y_829_ = v_queryPart_848_;
v___y_830_ = v___y_847_;
v___y_831_ = v___x_849_;
goto v___jp_822_;
}
else
{
lean_object* v_val_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_val_850_ = lean_ctor_get(v___y_839_, 0);
lean_inc(v_val_850_);
lean_dec_ref_known(v___y_839_, 1);
v___x_851_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__16));
v___x_852_ = l_Std_Http_URI_EncodedFragment_encode(v_val_850_);
lean_dec(v_val_850_);
v___x_853_ = lean_string_from_utf8_unchecked(v___x_852_);
v___x_854_ = lean_string_append(v___x_851_, v___x_853_);
lean_dec_ref(v___x_853_);
v___y_823_ = v___y_840_;
v___y_824_ = v___y_841_;
v___y_825_ = v___y_842_;
v___y_826_ = v___y_844_;
v___y_827_ = v___y_843_;
v___y_828_ = v___y_845_;
v___y_829_ = v_queryPart_848_;
v___y_830_ = v___y_847_;
v___y_831_ = v___x_854_;
goto v___jp_822_;
}
}
v___jp_855_:
{
lean_object* v_segments_865_; uint8_t v_absolute_866_; lean_object* v___x_867_; lean_object* v___x_868_; size_t v_sz_869_; size_t v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v_result_873_; 
v_segments_865_ = lean_ctor_get(v___y_863_, 0);
lean_inc_ref(v_segments_865_);
v_absolute_866_ = lean_ctor_get_uint8(v___y_863_, sizeof(void*)*1);
lean_dec_ref(v___y_863_);
v___x_867_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_868_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_869_ = lean_array_size(v_segments_865_);
v___x_870_ = ((size_t)0ULL);
v___x_871_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_868_, v___f_731_, v_sz_869_, v___x_870_, v_segments_865_);
v___x_872_ = lean_array_to_list(v___x_871_);
v_result_873_ = l_String_intercalate(v___x_867_, v___x_872_);
if (v_absolute_866_ == 0)
{
v___y_839_ = v___y_856_;
v___y_840_ = v___y_857_;
v___y_841_ = v___y_858_;
v___y_842_ = v___y_859_;
v___y_843_ = v___y_864_;
v___y_844_ = v___y_860_;
v___y_845_ = v___y_861_;
v___y_846_ = v___y_862_;
v___y_847_ = v_result_873_;
goto v___jp_838_;
}
else
{
lean_object* v___x_874_; 
v___x_874_ = lean_string_append(v___x_867_, v_result_873_);
lean_dec_ref(v_result_873_);
v___y_839_ = v___y_856_;
v___y_840_ = v___y_857_;
v___y_841_ = v___y_858_;
v___y_842_ = v___y_859_;
v___y_843_ = v___y_864_;
v___y_844_ = v___y_860_;
v___y_845_ = v___y_861_;
v___y_846_ = v___y_862_;
v___y_847_ = v___x_874_;
goto v___jp_838_;
}
}
v___jp_875_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_string_append(v___y_879_, v___y_882_);
lean_dec_ref(v___y_882_);
v___x_889_ = lean_string_append(v___x_888_, v___y_887_);
lean_dec_ref(v___y_887_);
lean_inc_ref(v___y_886_);
v___x_890_ = lean_string_append(v___y_886_, v___x_889_);
lean_dec_ref(v___x_889_);
v___y_856_ = v___y_876_;
v___y_857_ = v___y_877_;
v___y_858_ = v___y_878_;
v___y_859_ = v___y_880_;
v___y_860_ = v___y_881_;
v___y_861_ = v___y_883_;
v___y_862_ = v___y_884_;
v___y_863_ = v___y_885_;
v___y_864_ = v___x_890_;
goto v___jp_855_;
}
v___jp_891_:
{
switch(lean_obj_tag(v_port_899_))
{
case 0:
{
lean_object* v___x_904_; 
v___x_904_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_876_ = v___y_892_;
v___y_877_ = v___y_893_;
v___y_878_ = v___y_895_;
v___y_879_ = v___y_894_;
v___y_880_ = v___y_896_;
v___y_881_ = v___y_897_;
v___y_882_ = v___y_903_;
v___y_883_ = v___y_898_;
v___y_884_ = v___y_900_;
v___y_885_ = v___y_901_;
v___y_886_ = v___y_902_;
v___y_887_ = v___x_904_;
goto v___jp_875_;
}
case 1:
{
lean_object* v___x_905_; 
v___x_905_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_876_ = v___y_892_;
v___y_877_ = v___y_893_;
v___y_878_ = v___y_895_;
v___y_879_ = v___y_894_;
v___y_880_ = v___y_896_;
v___y_881_ = v___y_897_;
v___y_882_ = v___y_903_;
v___y_883_ = v___y_898_;
v___y_884_ = v___y_900_;
v___y_885_ = v___y_901_;
v___y_886_ = v___y_902_;
v___y_887_ = v___x_905_;
goto v___jp_875_;
}
default: 
{
uint16_t v_port_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_port_906_ = lean_ctor_get_uint16(v_port_899_, 0);
lean_dec_ref_known(v_port_899_, 0);
v___x_907_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_908_ = lean_uint16_to_nat(v_port_906_);
v___x_909_ = l_Nat_reprFast(v___x_908_);
v___x_910_ = lean_string_append(v___x_907_, v___x_909_);
lean_dec_ref(v___x_909_);
v___y_876_ = v___y_892_;
v___y_877_ = v___y_893_;
v___y_878_ = v___y_895_;
v___y_879_ = v___y_894_;
v___y_880_ = v___y_896_;
v___y_881_ = v___y_897_;
v___y_882_ = v___y_903_;
v___y_883_ = v___y_898_;
v___y_884_ = v___y_900_;
v___y_885_ = v___y_901_;
v___y_886_ = v___y_902_;
v___y_887_ = v___x_910_;
goto v___jp_875_;
}
}
}
v___jp_911_:
{
switch(lean_obj_tag(v_host_918_))
{
case 0:
{
lean_object* v_name_924_; 
v_name_924_ = lean_ctor_get(v_host_918_, 0);
lean_inc_ref(v_name_924_);
lean_dec_ref_known(v_host_918_, 1);
v___y_892_ = v___y_912_;
v___y_893_ = v___y_913_;
v___y_894_ = v___y_923_;
v___y_895_ = v___y_914_;
v___y_896_ = v___y_915_;
v___y_897_ = v___y_916_;
v___y_898_ = v___y_917_;
v_port_899_ = v_port_919_;
v___y_900_ = v___y_920_;
v___y_901_ = v___y_921_;
v___y_902_ = v___y_922_;
v___y_903_ = v_name_924_;
goto v___jp_891_;
}
case 1:
{
lean_object* v_ipv4_925_; lean_object* v___x_926_; 
v_ipv4_925_ = lean_ctor_get(v_host_918_, 0);
lean_inc_ref(v_ipv4_925_);
lean_dec_ref_known(v_host_918_, 1);
v___x_926_ = lean_uv_ntop_v4(v_ipv4_925_);
lean_dec_ref(v_ipv4_925_);
v___y_892_ = v___y_912_;
v___y_893_ = v___y_913_;
v___y_894_ = v___y_923_;
v___y_895_ = v___y_914_;
v___y_896_ = v___y_915_;
v___y_897_ = v___y_916_;
v___y_898_ = v___y_917_;
v_port_899_ = v_port_919_;
v___y_900_ = v___y_920_;
v___y_901_ = v___y_921_;
v___y_902_ = v___y_922_;
v___y_903_ = v___x_926_;
goto v___jp_891_;
}
default: 
{
lean_object* v_ipv6_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_ipv6_927_ = lean_ctor_get(v_host_918_, 0);
lean_inc_ref(v_ipv6_927_);
lean_dec_ref_known(v_host_918_, 1);
v___x_928_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_929_ = lean_uv_ntop_v6(v_ipv6_927_);
lean_dec_ref(v_ipv6_927_);
v___x_930_ = lean_string_append(v___x_928_, v___x_929_);
lean_dec_ref(v___x_929_);
v___x_931_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_932_ = lean_string_append(v___x_930_, v___x_931_);
v___y_892_ = v___y_912_;
v___y_893_ = v___y_913_;
v___y_894_ = v___y_923_;
v___y_895_ = v___y_914_;
v___y_896_ = v___y_915_;
v___y_897_ = v___y_916_;
v___y_898_ = v___y_917_;
v_port_899_ = v_port_919_;
v___y_900_ = v___y_920_;
v___y_901_ = v___y_921_;
v___y_902_ = v___y_922_;
v___y_903_ = v___x_932_;
goto v___jp_891_;
}
}
}
v___jp_933_:
{
lean_object* v_queryStr_940_; lean_object* v___x_941_; 
v_queryStr_940_ = l_Std_Http_URI_Query_formatOption(v___y_938_);
v___x_941_ = lean_string_append(v___y_939_, v_queryStr_940_);
lean_dec_ref(v_queryStr_940_);
v___y_765_ = v___y_934_;
v___y_766_ = v___y_935_;
v___y_767_ = v___y_936_;
v___y_768_ = v___y_937_;
v___y_769_ = v___x_941_;
goto v___jp_764_;
}
v___jp_942_:
{
lean_object* v_data_944_; lean_object* v_size_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v_data_944_ = lean_ctor_get(v_buffer_733_, 0);
lean_inc_ref(v_data_944_);
v_size_945_ = lean_ctor_get(v_buffer_733_, 1);
lean_inc(v_size_945_);
lean_dec_ref(v_buffer_733_);
v___x_946_ = lean_string_to_utf8(v___y_943_);
lean_inc_ref(v___x_946_);
v___x_947_ = lean_array_push(v_data_944_, v___x_946_);
v___x_948_ = lean_byte_array_size(v___x_946_);
lean_dec_ref(v___x_946_);
v___x_949_ = lean_nat_add(v_size_945_, v___x_948_);
lean_dec(v_size_945_);
v___x_950_ = ((lean_object*)(l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2));
v___x_951_ = lean_array_push(v___x_947_, v___x_950_);
v___x_952_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3);
v___x_953_ = lean_nat_add(v___x_949_, v___x_952_);
lean_dec(v___x_949_);
switch(lean_obj_tag(v_uri_737_))
{
case 0:
{
lean_object* v_path_954_; lean_object* v_query_955_; lean_object* v_segments_956_; uint8_t v_absolute_957_; lean_object* v___x_958_; lean_object* v___x_959_; size_t v_sz_960_; size_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v_result_964_; 
lean_dec_ref(v___f_731_);
v_path_954_ = lean_ctor_get(v_uri_737_, 0);
lean_inc_ref(v_path_954_);
v_query_955_ = lean_ctor_get(v_uri_737_, 1);
lean_inc(v_query_955_);
lean_dec_ref_known(v_uri_737_, 2);
v_segments_956_ = lean_ctor_get(v_path_954_, 0);
lean_inc_ref(v_segments_956_);
v_absolute_957_ = lean_ctor_get_uint8(v_path_954_, sizeof(void*)*1);
lean_dec_ref(v_path_954_);
v___x_958_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_959_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_960_ = lean_array_size(v_segments_956_);
v___x_961_ = ((size_t)0ULL);
v___x_962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_959_, v___f_732_, v_sz_960_, v___x_961_, v_segments_956_);
v___x_963_ = lean_array_to_list(v___x_962_);
v_result_964_ = l_String_intercalate(v___x_958_, v___x_963_);
if (v_absolute_957_ == 0)
{
v___y_934_ = v___x_951_;
v___y_935_ = v___x_950_;
v___y_936_ = v___x_953_;
v___y_937_ = v___x_952_;
v___y_938_ = v_query_955_;
v___y_939_ = v_result_964_;
goto v___jp_933_;
}
else
{
lean_object* v___x_965_; 
v___x_965_ = lean_string_append(v___x_958_, v_result_964_);
lean_dec_ref(v_result_964_);
v___y_934_ = v___x_951_;
v___y_935_ = v___x_950_;
v___y_936_ = v___x_953_;
v___y_937_ = v___x_952_;
v___y_938_ = v_query_955_;
v___y_939_ = v___x_965_;
goto v___jp_933_;
}
}
case 1:
{
lean_object* v_uri_966_; lean_object* v_authority_967_; 
lean_dec_ref(v___f_732_);
v_uri_966_ = lean_ctor_get(v_uri_737_, 0);
lean_inc_ref(v_uri_966_);
lean_dec_ref_known(v_uri_737_, 1);
v_authority_967_ = lean_ctor_get(v_uri_966_, 1);
if (lean_obj_tag(v_authority_967_) == 0)
{
lean_object* v_scheme_968_; lean_object* v_path_969_; lean_object* v_query_970_; lean_object* v_fragment_971_; lean_object* v___x_972_; 
v_scheme_968_ = lean_ctor_get(v_uri_966_, 0);
lean_inc_ref(v_scheme_968_);
v_path_969_ = lean_ctor_get(v_uri_966_, 2);
lean_inc_ref(v_path_969_);
v_query_970_ = lean_ctor_get(v_uri_966_, 3);
lean_inc(v_query_970_);
v_fragment_971_ = lean_ctor_get(v_uri_966_, 4);
lean_inc(v_fragment_971_);
lean_dec_ref(v_uri_966_);
v___x_972_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_856_ = v_fragment_971_;
v___y_857_ = v___x_951_;
v___y_858_ = v___x_950_;
v___y_859_ = v_scheme_968_;
v___y_860_ = v___x_953_;
v___y_861_ = v___x_952_;
v___y_862_ = v_query_970_;
v___y_863_ = v_path_969_;
v___y_864_ = v___x_972_;
goto v___jp_855_;
}
else
{
lean_object* v_val_973_; lean_object* v_scheme_974_; lean_object* v_path_975_; lean_object* v_query_976_; lean_object* v_fragment_977_; lean_object* v_userInfo_978_; lean_object* v_host_979_; lean_object* v_port_980_; lean_object* v___x_981_; 
v_val_973_ = lean_ctor_get(v_authority_967_, 0);
lean_inc(v_val_973_);
v_scheme_974_ = lean_ctor_get(v_uri_966_, 0);
lean_inc_ref(v_scheme_974_);
v_path_975_ = lean_ctor_get(v_uri_966_, 2);
lean_inc_ref(v_path_975_);
v_query_976_ = lean_ctor_get(v_uri_966_, 3);
lean_inc(v_query_976_);
v_fragment_977_ = lean_ctor_get(v_uri_966_, 4);
lean_inc(v_fragment_977_);
lean_dec_ref(v_uri_966_);
v_userInfo_978_ = lean_ctor_get(v_val_973_, 0);
lean_inc(v_userInfo_978_);
v_host_979_ = lean_ctor_get(v_val_973_, 1);
lean_inc_ref(v_host_979_);
v_port_980_ = lean_ctor_get(v_val_973_, 2);
lean_inc(v_port_980_);
lean_dec(v_val_973_);
v___x_981_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__21));
if (lean_obj_tag(v_userInfo_978_) == 0)
{
lean_object* v___x_982_; 
v___x_982_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_912_ = v_fragment_977_;
v___y_913_ = v___x_951_;
v___y_914_ = v___x_950_;
v___y_915_ = v_scheme_974_;
v___y_916_ = v___x_953_;
v___y_917_ = v___x_952_;
v_host_918_ = v_host_979_;
v_port_919_ = v_port_980_;
v___y_920_ = v_query_976_;
v___y_921_ = v_path_975_;
v___y_922_ = v___x_981_;
v___y_923_ = v___x_982_;
goto v___jp_911_;
}
else
{
lean_object* v_val_983_; lean_object* v_password_984_; 
v_val_983_ = lean_ctor_get(v_userInfo_978_, 0);
lean_inc(v_val_983_);
lean_dec_ref_known(v_userInfo_978_, 1);
v_password_984_ = lean_ctor_get(v_val_983_, 1);
if (lean_obj_tag(v_password_984_) == 0)
{
lean_object* v_username_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_username_985_ = lean_ctor_get(v_val_983_, 0);
lean_inc_ref(v_username_985_);
lean_dec(v_val_983_);
v___x_986_ = lean_string_from_utf8_unchecked(v_username_985_);
v___x_987_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_988_ = lean_string_append(v___x_986_, v___x_987_);
v___y_912_ = v_fragment_977_;
v___y_913_ = v___x_951_;
v___y_914_ = v___x_950_;
v___y_915_ = v_scheme_974_;
v___y_916_ = v___x_953_;
v___y_917_ = v___x_952_;
v_host_918_ = v_host_979_;
v_port_919_ = v_port_980_;
v___y_920_ = v_query_976_;
v___y_921_ = v_path_975_;
v___y_922_ = v___x_981_;
v___y_923_ = v___x_988_;
goto v___jp_911_;
}
else
{
lean_object* v_username_989_; lean_object* v_val_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
lean_inc_ref(v_password_984_);
v_username_989_ = lean_ctor_get(v_val_983_, 0);
lean_inc_ref(v_username_989_);
lean_dec(v_val_983_);
v_val_990_ = lean_ctor_get(v_password_984_, 0);
lean_inc(v_val_990_);
lean_dec_ref_known(v_password_984_, 1);
v___x_991_ = lean_string_from_utf8_unchecked(v_username_989_);
v___x_992_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_993_ = lean_string_append(v___x_991_, v___x_992_);
v___x_994_ = lean_string_from_utf8_unchecked(v_val_990_);
v___x_995_ = lean_string_append(v___x_993_, v___x_994_);
lean_dec_ref(v___x_994_);
v___x_996_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_997_ = lean_string_append(v___x_995_, v___x_996_);
v___y_912_ = v_fragment_977_;
v___y_913_ = v___x_951_;
v___y_914_ = v___x_950_;
v___y_915_ = v_scheme_974_;
v___y_916_ = v___x_953_;
v___y_917_ = v___x_952_;
v_host_918_ = v_host_979_;
v_port_919_ = v_port_980_;
v___y_920_ = v_query_976_;
v___y_921_ = v_path_975_;
v___y_922_ = v___x_981_;
v___y_923_ = v___x_997_;
goto v___jp_911_;
}
}
}
}
case 2:
{
lean_object* v_authority_998_; lean_object* v_userInfo_999_; 
lean_dec_ref(v___f_732_);
lean_dec_ref(v___f_731_);
v_authority_998_ = lean_ctor_get(v_uri_737_, 0);
lean_inc_ref(v_authority_998_);
lean_dec_ref_known(v_uri_737_, 1);
v_userInfo_999_ = lean_ctor_get(v_authority_998_, 0);
if (lean_obj_tag(v_userInfo_999_) == 0)
{
lean_object* v_host_1000_; lean_object* v_port_1001_; lean_object* v___x_1002_; 
v_host_1000_ = lean_ctor_get(v_authority_998_, 1);
lean_inc_ref(v_host_1000_);
v_port_1001_ = lean_ctor_get(v_authority_998_, 2);
lean_inc(v_port_1001_);
lean_dec_ref(v_authority_998_);
v___x_1002_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_806_ = v___x_951_;
v_host_807_ = v_host_1000_;
v_port_808_ = v_port_1001_;
v___y_809_ = v___x_950_;
v___y_810_ = v___x_953_;
v___y_811_ = v___x_952_;
v___y_812_ = v___x_1002_;
goto v___jp_805_;
}
else
{
lean_object* v_val_1003_; lean_object* v_password_1004_; 
v_val_1003_ = lean_ctor_get(v_userInfo_999_, 0);
lean_inc(v_val_1003_);
v_password_1004_ = lean_ctor_get(v_val_1003_, 1);
if (lean_obj_tag(v_password_1004_) == 0)
{
lean_object* v_host_1005_; lean_object* v_port_1006_; lean_object* v_username_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_host_1005_ = lean_ctor_get(v_authority_998_, 1);
lean_inc_ref(v_host_1005_);
v_port_1006_ = lean_ctor_get(v_authority_998_, 2);
lean_inc(v_port_1006_);
lean_dec_ref(v_authority_998_);
v_username_1007_ = lean_ctor_get(v_val_1003_, 0);
lean_inc_ref(v_username_1007_);
lean_dec(v_val_1003_);
v___x_1008_ = lean_string_from_utf8_unchecked(v_username_1007_);
v___x_1009_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_1010_ = lean_string_append(v___x_1008_, v___x_1009_);
v___y_806_ = v___x_951_;
v_host_807_ = v_host_1005_;
v_port_808_ = v_port_1006_;
v___y_809_ = v___x_950_;
v___y_810_ = v___x_953_;
v___y_811_ = v___x_952_;
v___y_812_ = v___x_1010_;
goto v___jp_805_;
}
else
{
lean_object* v_host_1011_; lean_object* v_port_1012_; lean_object* v_username_1013_; lean_object* v_val_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_inc_ref(v_password_1004_);
v_host_1011_ = lean_ctor_get(v_authority_998_, 1);
lean_inc_ref(v_host_1011_);
v_port_1012_ = lean_ctor_get(v_authority_998_, 2);
lean_inc(v_port_1012_);
lean_dec_ref(v_authority_998_);
v_username_1013_ = lean_ctor_get(v_val_1003_, 0);
lean_inc_ref(v_username_1013_);
lean_dec(v_val_1003_);
v_val_1014_ = lean_ctor_get(v_password_1004_, 0);
lean_inc(v_val_1014_);
lean_dec_ref_known(v_password_1004_, 1);
v___x_1015_ = lean_string_from_utf8_unchecked(v_username_1013_);
v___x_1016_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_1017_ = lean_string_append(v___x_1015_, v___x_1016_);
v___x_1018_ = lean_string_from_utf8_unchecked(v_val_1014_);
v___x_1019_ = lean_string_append(v___x_1017_, v___x_1018_);
lean_dec_ref(v___x_1018_);
v___x_1020_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_1021_ = lean_string_append(v___x_1019_, v___x_1020_);
v___y_806_ = v___x_951_;
v_host_807_ = v_host_1011_;
v_port_808_ = v_port_1012_;
v___y_809_ = v___x_950_;
v___y_810_ = v___x_953_;
v___y_811_ = v___x_952_;
v___y_812_ = v___x_1021_;
goto v___jp_805_;
}
}
}
default: 
{
lean_object* v___x_1022_; 
lean_dec_ref(v___f_732_);
lean_dec_ref(v___f_731_);
v___x_1022_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__23));
v___y_765_ = v___x_951_;
v___y_766_ = v___x_950_;
v___y_767_ = v___x_953_;
v___y_768_ = v___x_952_;
v___y_769_ = v___x_1022_;
goto v___jp_764_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__0(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; uint8_t v___x_1071_; lean_object* v___x_1072_; 
v___x_1068_ = l_Std_Http_Headers_empty;
v___x_1069_ = lean_box(3);
v___x_1070_ = 1;
v___x_1071_ = 8;
v___x_1072_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1072_, 0, v___x_1069_);
lean_ctor_set(v___x_1072_, 1, v___x_1068_);
lean_ctor_set_uint8(v___x_1072_, sizeof(void*)*2, v___x_1071_);
lean_ctor_set_uint8(v___x_1072_, sizeof(void*)*2 + 1, v___x_1070_);
return v___x_1072_;
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__1(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1073_ = l_Std_Http_Extensions_empty;
v___x_1074_ = lean_obj_once(&l_Std_Http_Request_new___closed__0, &l_Std_Http_Request_new___closed__0_once, _init_l_Std_Http_Request_new___closed__0);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v___x_1073_);
return v___x_1075_;
}
}
static lean_object* _init_l_Std_Http_Request_new(void){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_obj_once(&l_Std_Http_Request_new___closed__1, &l_Std_Http_Request_new___closed__1_once, _init_l_Std_Http_Request_new___closed__1);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method(lean_object* v_builder_1077_, uint8_t v_method_1078_){
_start:
{
lean_object* v_line_1079_; lean_object* v_extensions_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1097_; 
v_line_1079_ = lean_ctor_get(v_builder_1077_, 0);
v_extensions_1080_ = lean_ctor_get(v_builder_1077_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_builder_1077_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1082_ = v_builder_1077_;
v_isShared_1083_ = v_isSharedCheck_1097_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_extensions_1080_);
lean_inc(v_line_1079_);
lean_dec(v_builder_1077_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1097_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
uint8_t v_version_1084_; lean_object* v_uri_1085_; lean_object* v_headers_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1096_; 
v_version_1084_ = lean_ctor_get_uint8(v_line_1079_, sizeof(void*)*2 + 1);
v_uri_1085_ = lean_ctor_get(v_line_1079_, 0);
v_headers_1086_ = lean_ctor_get(v_line_1079_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_line_1079_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1088_ = v_line_1079_;
v_isShared_1089_ = v_isSharedCheck_1096_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_headers_1086_);
lean_inc(v_uri_1085_);
lean_dec(v_line_1079_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1096_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_uri_1085_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_headers_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1095_, sizeof(void*)*2 + 1, v_version_1084_);
v___x_1091_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1093_; 
lean_ctor_set_uint8(v___x_1091_, sizeof(void*)*2, v_method_1078_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1091_);
v___x_1093_ = v___x_1082_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_extensions_1080_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method___boxed(lean_object* v_builder_1098_, lean_object* v_method_1099_){
_start:
{
uint8_t v_method_boxed_1100_; lean_object* v_res_1101_; 
v_method_boxed_1100_ = lean_unbox(v_method_1099_);
v_res_1101_ = l_Std_Http_Request_Builder_method(v_builder_1098_, v_method_boxed_1100_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version(lean_object* v_builder_1102_, uint8_t v_version_1103_){
_start:
{
lean_object* v_line_1104_; lean_object* v_extensions_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1122_; 
v_line_1104_ = lean_ctor_get(v_builder_1102_, 0);
v_extensions_1105_ = lean_ctor_get(v_builder_1102_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_builder_1102_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1107_ = v_builder_1102_;
v_isShared_1108_ = v_isSharedCheck_1122_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_extensions_1105_);
lean_inc(v_line_1104_);
lean_dec(v_builder_1102_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1122_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
uint8_t v_method_1109_; lean_object* v_uri_1110_; lean_object* v_headers_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1121_; 
v_method_1109_ = lean_ctor_get_uint8(v_line_1104_, sizeof(void*)*2);
v_uri_1110_ = lean_ctor_get(v_line_1104_, 0);
v_headers_1111_ = lean_ctor_get(v_line_1104_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_line_1104_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1113_ = v_line_1104_;
v_isShared_1114_ = v_isSharedCheck_1121_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_headers_1111_);
lean_inc(v_uri_1110_);
lean_dec(v_line_1104_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1121_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_uri_1110_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_headers_1111_);
lean_ctor_set_uint8(v_reuseFailAlloc_1120_, sizeof(void*)*2, v_method_1109_);
v___x_1116_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1118_; 
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*2 + 1, v_version_1103_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1116_);
v___x_1118_ = v___x_1107_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_extensions_1105_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version___boxed(lean_object* v_builder_1123_, lean_object* v_version_1124_){
_start:
{
uint8_t v_version_boxed_1125_; lean_object* v_res_1126_; 
v_version_boxed_1125_ = lean_unbox(v_version_1124_);
v_res_1126_ = l_Std_Http_Request_Builder_version(v_builder_1123_, v_version_boxed_1125_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri(lean_object* v_builder_1127_, lean_object* v_uri_1128_){
_start:
{
lean_object* v_line_1129_; lean_object* v_extensions_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1148_; 
v_line_1129_ = lean_ctor_get(v_builder_1127_, 0);
v_extensions_1130_ = lean_ctor_get(v_builder_1127_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_builder_1127_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1132_ = v_builder_1127_;
v_isShared_1133_ = v_isSharedCheck_1148_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_extensions_1130_);
lean_inc(v_line_1129_);
lean_dec(v_builder_1127_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1148_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
uint8_t v_method_1134_; uint8_t v_version_1135_; lean_object* v_headers_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1146_; 
v_method_1134_ = lean_ctor_get_uint8(v_line_1129_, sizeof(void*)*2);
v_version_1135_ = lean_ctor_get_uint8(v_line_1129_, sizeof(void*)*2 + 1);
v_headers_1136_ = lean_ctor_get(v_line_1129_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_line_1129_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; 
v_unused_1147_ = lean_ctor_get(v_line_1129_, 0);
lean_dec(v_unused_1147_);
v___x_1138_ = v_line_1129_;
v_isShared_1139_ = v_isSharedCheck_1146_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_headers_1136_);
lean_dec(v_line_1129_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1146_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v_uri_1128_);
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_uri_1128_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_headers_1136_);
lean_ctor_set_uint8(v_reuseFailAlloc_1145_, sizeof(void*)*2, v_method_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1145_, sizeof(void*)*2 + 1, v_version_1135_);
v___x_1141_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1143_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1141_);
v___x_1143_ = v___x_1132_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_extensions_1130_);
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
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(lean_object* v_msg_1149_){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = l_Std_Http_instInhabitedRequestTarget_default;
v___x_1151_ = lean_panic_fn_borrowed(v___x_1150_, v_msg_1149_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___lam__0(lean_object* v___x_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_pos_1158_; lean_object* v_array_1159_; lean_object* v_idx_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v_pos_1158_ = lean_ctor_get(v___x_1157_, 0);
v_array_1159_ = lean_ctor_get(v_pos_1158_, 0);
v_idx_1160_ = lean_ctor_get(v_pos_1158_, 1);
v___x_1161_ = lean_byte_array_size(v_array_1159_);
v___x_1162_ = lean_nat_dec_lt(v_idx_1160_, v___x_1161_);
if (v___x_1162_ == 0)
{
return v___x_1157_;
}
else
{
lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1170_; 
lean_inc(v_pos_1158_);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; lean_object* v_unused_1172_; 
v_unused_1171_ = lean_ctor_get(v___x_1157_, 1);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v___x_1157_, 0);
lean_dec(v_unused_1172_);
v___x_1164_ = v___x_1157_;
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
else
{
lean_dec(v___x_1157_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___lam__0___closed__1));
if (v_isShared_1165_ == 0)
{
lean_ctor_set_tag(v___x_1164_, 1);
lean_ctor_set(v___x_1164_, 1, v___x_1166_);
v___x_1168_ = v___x_1164_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_pos_1158_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v___x_1166_);
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
else
{
return v___x_1157_;
}
}
}
static lean_object* _init_l_Std_Http_Request_Builder_uri_x21___closed__5(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1186_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__4));
v___x_1187_ = lean_unsigned_to_nat(12u);
v___x_1188_ = lean_unsigned_to_nat(45u);
v___x_1189_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__3));
v___x_1190_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__2));
v___x_1191_ = l_mkPanicMessageWithDecl(v___x_1190_, v___x_1189_, v___x_1188_, v___x_1187_, v___x_1186_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21(lean_object* v_builder_1192_, lean_object* v_uri_1193_){
_start:
{
lean_object* v___y_1195_; lean_object* v___f_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___f_1216_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__1));
v___x_1217_ = lean_string_to_utf8(v_uri_1193_);
v___x_1218_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1216_, v___x_1217_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_dec_ref_known(v___x_1218_, 1);
v___x_1219_ = lean_obj_once(&l_Std_Http_Request_Builder_uri_x21___closed__5, &l_Std_Http_Request_Builder_uri_x21___closed__5_once, _init_l_Std_Http_Request_Builder_uri_x21___closed__5);
v___x_1220_ = l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(v___x_1219_);
v___y_1195_ = v___x_1220_;
goto v___jp_1194_;
}
else
{
lean_object* v_a_1221_; 
v_a_1221_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1218_, 1);
v___y_1195_ = v_a_1221_;
goto v___jp_1194_;
}
v___jp_1194_:
{
lean_object* v_line_1196_; lean_object* v_extensions_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1215_; 
v_line_1196_ = lean_ctor_get(v_builder_1192_, 0);
v_extensions_1197_ = lean_ctor_get(v_builder_1192_, 1);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_builder_1192_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1199_ = v_builder_1192_;
v_isShared_1200_ = v_isSharedCheck_1215_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_extensions_1197_);
lean_inc(v_line_1196_);
lean_dec(v_builder_1192_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1215_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
uint8_t v_method_1201_; uint8_t v_version_1202_; lean_object* v_headers_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1213_; 
v_method_1201_ = lean_ctor_get_uint8(v_line_1196_, sizeof(void*)*2);
v_version_1202_ = lean_ctor_get_uint8(v_line_1196_, sizeof(void*)*2 + 1);
v_headers_1203_ = lean_ctor_get(v_line_1196_, 1);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_line_1196_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v_line_1196_, 0);
lean_dec(v_unused_1214_);
v___x_1205_ = v_line_1196_;
v_isShared_1206_ = v_isSharedCheck_1213_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_headers_1203_);
lean_dec(v_line_1196_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1213_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___y_1195_);
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___y_1195_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_headers_1203_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*2, v_method_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*2 + 1, v_version_1202_);
v___x_1208_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1210_; 
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v___x_1208_);
v___x_1210_ = v___x_1199_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_extensions_1197_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___boxed(lean_object* v_builder_1222_, lean_object* v_uri_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Std_Http_Request_Builder_uri_x21(v_builder_1222_, v_uri_1223_);
lean_dec_ref(v_uri_1223_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headers(lean_object* v_builder_1225_, lean_object* v_headers_1226_){
_start:
{
lean_object* v_line_1227_; lean_object* v_extensions_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1246_; 
v_line_1227_ = lean_ctor_get(v_builder_1225_, 0);
v_extensions_1228_ = lean_ctor_get(v_builder_1225_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_builder_1225_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1230_ = v_builder_1225_;
v_isShared_1231_ = v_isSharedCheck_1246_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_extensions_1228_);
lean_inc(v_line_1227_);
lean_dec(v_builder_1225_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1246_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
uint8_t v_method_1232_; uint8_t v_version_1233_; lean_object* v_uri_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1244_; 
v_method_1232_ = lean_ctor_get_uint8(v_line_1227_, sizeof(void*)*2);
v_version_1233_ = lean_ctor_get_uint8(v_line_1227_, sizeof(void*)*2 + 1);
v_uri_1234_ = lean_ctor_get(v_line_1227_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_line_1227_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; 
v_unused_1245_ = lean_ctor_get(v_line_1227_, 1);
lean_dec(v_unused_1245_);
v___x_1236_ = v_line_1227_;
v_isShared_1237_ = v_isSharedCheck_1244_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_uri_1234_);
lean_dec(v_line_1227_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1244_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 1, v_headers_1226_);
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_uri_1234_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_headers_1226_);
lean_ctor_set_uint8(v_reuseFailAlloc_1243_, sizeof(void*)*2, v_method_1232_);
lean_ctor_set_uint8(v_reuseFailAlloc_1243_, sizeof(void*)*2 + 1, v_version_1233_);
v___x_1239_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1241_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v___x_1239_);
v___x_1241_ = v___x_1230_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_extensions_1228_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(lean_object* v_i_1247_, lean_object* v_x_1248_){
_start:
{
if (lean_obj_tag(v_x_1248_) == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1249_ = lean_unsigned_to_nat(1u);
v___x_1250_ = lean_mk_empty_array_with_capacity(v___x_1249_);
v___x_1251_ = lean_array_push(v___x_1250_, v_i_1247_);
v___x_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
return v___x_1252_;
}
else
{
lean_object* v_val_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1261_; 
v_val_1253_ = lean_ctor_get(v_x_1248_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_x_1248_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1255_ = v_x_1248_;
v_isShared_1256_ = v_isSharedCheck_1261_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_val_1253_);
lean_dec(v_x_1248_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1261_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1257_ = lean_array_push(v_val_1253_, v_i_1247_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1257_);
v___x_1259_ = v___x_1255_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(lean_object* v_i_1262_, lean_object* v_a_1263_, lean_object* v_x_1264_){
_start:
{
if (lean_obj_tag(v_x_1264_) == 0)
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_val_1267_; lean_object* v___x_1268_; 
v___x_1265_ = lean_box(0);
v___x_1266_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(v_i_1262_, v___x_1265_);
v_val_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_val_1267_);
lean_dec(v___x_1266_);
v___x_1268_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1268_, 0, v_a_1263_);
lean_ctor_set(v___x_1268_, 1, v_val_1267_);
lean_ctor_set(v___x_1268_, 2, v_x_1264_);
return v___x_1268_;
}
else
{
lean_object* v_key_1269_; lean_object* v_value_1270_; lean_object* v_tail_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1286_; 
v_key_1269_ = lean_ctor_get(v_x_1264_, 0);
v_value_1270_ = lean_ctor_get(v_x_1264_, 1);
v_tail_1271_ = lean_ctor_get(v_x_1264_, 2);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_x_1264_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1273_ = v_x_1264_;
v_isShared_1274_ = v_isSharedCheck_1286_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_tail_1271_);
lean_inc(v_value_1270_);
lean_inc(v_key_1269_);
lean_dec(v_x_1264_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1286_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
uint8_t v___x_1275_; 
v___x_1275_ = lean_string_dec_eq(v_key_1269_, v_a_1263_);
if (v___x_1275_ == 0)
{
lean_object* v_tail_1276_; lean_object* v___x_1278_; 
v_tail_1276_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_1262_, v_a_1263_, v_tail_1271_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 2, v_tail_1276_);
v___x_1278_ = v___x_1273_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_key_1269_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_value_1270_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v_tail_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v_val_1282_; lean_object* v___x_1284_; 
lean_dec(v_key_1269_);
v___x_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1280_, 0, v_value_1270_);
v___x_1281_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(v_i_1262_, v___x_1280_);
v_val_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_val_1282_);
lean_dec(v___x_1281_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v_val_1282_);
lean_ctor_set(v___x_1273_, 0, v_a_1263_);
v___x_1284_ = v___x_1273_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1263_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_val_1282_);
lean_ctor_set(v_reuseFailAlloc_1285_, 2, v_tail_1271_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(lean_object* v_a_1287_, lean_object* v_x_1288_){
_start:
{
if (lean_obj_tag(v_x_1288_) == 0)
{
uint8_t v___x_1289_; 
v___x_1289_ = 0;
return v___x_1289_;
}
else
{
lean_object* v_key_1290_; lean_object* v_tail_1291_; uint8_t v___x_1292_; 
v_key_1290_ = lean_ctor_get(v_x_1288_, 0);
v_tail_1291_ = lean_ctor_get(v_x_1288_, 2);
v___x_1292_ = lean_string_dec_eq(v_key_1290_, v_a_1287_);
if (v___x_1292_ == 0)
{
v_x_1288_ = v_tail_1291_;
goto _start;
}
else
{
return v___x_1292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg___boxed(lean_object* v_a_1294_, lean_object* v_x_1295_){
_start:
{
uint8_t v_res_1296_; lean_object* v_r_1297_; 
v_res_1296_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1294_, v_x_1295_);
lean_dec(v_x_1295_);
lean_dec_ref(v_a_1294_);
v_r_1297_ = lean_box(v_res_1296_);
return v_r_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1298_, lean_object* v_x_1299_){
_start:
{
if (lean_obj_tag(v_x_1299_) == 0)
{
return v_x_1298_;
}
else
{
lean_object* v_key_1300_; lean_object* v_value_1301_; lean_object* v_tail_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1325_; 
v_key_1300_ = lean_ctor_get(v_x_1299_, 0);
v_value_1301_ = lean_ctor_get(v_x_1299_, 1);
v_tail_1302_ = lean_ctor_get(v_x_1299_, 2);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_x_1299_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1304_ = v_x_1299_;
v_isShared_1305_ = v_isSharedCheck_1325_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_tail_1302_);
lean_inc(v_value_1301_);
lean_inc(v_key_1300_);
lean_dec(v_x_1299_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1325_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; uint64_t v___x_1307_; uint64_t v___x_1308_; uint64_t v___x_1309_; uint64_t v_fold_1310_; uint64_t v___x_1311_; uint64_t v___x_1312_; uint64_t v___x_1313_; size_t v___x_1314_; size_t v___x_1315_; size_t v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1306_ = lean_array_get_size(v_x_1298_);
v___x_1307_ = lean_string_hash(v_key_1300_);
v___x_1308_ = 32ULL;
v___x_1309_ = lean_uint64_shift_right(v___x_1307_, v___x_1308_);
v_fold_1310_ = lean_uint64_xor(v___x_1307_, v___x_1309_);
v___x_1311_ = 16ULL;
v___x_1312_ = lean_uint64_shift_right(v_fold_1310_, v___x_1311_);
v___x_1313_ = lean_uint64_xor(v_fold_1310_, v___x_1312_);
v___x_1314_ = lean_uint64_to_usize(v___x_1313_);
v___x_1315_ = lean_usize_of_nat(v___x_1306_);
v___x_1316_ = ((size_t)1ULL);
v___x_1317_ = lean_usize_sub(v___x_1315_, v___x_1316_);
v___x_1318_ = lean_usize_land(v___x_1314_, v___x_1317_);
v___x_1319_ = lean_array_uget_borrowed(v_x_1298_, v___x_1318_);
lean_inc(v___x_1319_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 2, v___x_1319_);
v___x_1321_ = v___x_1304_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_key_1300_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_value_1301_);
lean_ctor_set(v_reuseFailAlloc_1324_, 2, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; 
v___x_1322_ = lean_array_uset(v_x_1298_, v___x_1318_, v___x_1321_);
v_x_1298_ = v___x_1322_;
v_x_1299_ = v_tail_1302_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1326_, lean_object* v_source_1327_, lean_object* v_target_1328_){
_start:
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = lean_array_get_size(v_source_1327_);
v___x_1330_ = lean_nat_dec_lt(v_i_1326_, v___x_1329_);
if (v___x_1330_ == 0)
{
lean_dec_ref(v_source_1327_);
lean_dec(v_i_1326_);
return v_target_1328_;
}
else
{
lean_object* v_es_1331_; lean_object* v___x_1332_; lean_object* v_source_1333_; lean_object* v_target_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v_es_1331_ = lean_array_fget(v_source_1327_, v_i_1326_);
v___x_1332_ = lean_box(0);
v_source_1333_ = lean_array_fset(v_source_1327_, v_i_1326_, v___x_1332_);
v_target_1334_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1328_, v_es_1331_);
v___x_1335_ = lean_unsigned_to_nat(1u);
v___x_1336_ = lean_nat_add(v_i_1326_, v___x_1335_);
lean_dec(v_i_1326_);
v_i_1326_ = v___x_1336_;
v_source_1327_ = v_source_1333_;
v_target_1328_ = v_target_1334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(lean_object* v_data_1338_){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v_nbuckets_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1339_ = lean_array_get_size(v_data_1338_);
v___x_1340_ = lean_unsigned_to_nat(2u);
v_nbuckets_1341_ = lean_nat_mul(v___x_1339_, v___x_1340_);
v___x_1342_ = lean_unsigned_to_nat(0u);
v___x_1343_ = lean_box(0);
v___x_1344_ = lean_mk_array(v_nbuckets_1341_, v___x_1343_);
v___x_1345_ = lean_array_propagate_mark(v_data_1338_, v___x_1344_);
v___x_1346_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v___x_1342_, v_data_1338_, v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(lean_object* v_i_1347_, lean_object* v_m_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_size_1350_; lean_object* v_buckets_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1401_; 
v_size_1350_ = lean_ctor_get(v_m_1348_, 0);
v_buckets_1351_ = lean_ctor_get(v_m_1348_, 1);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_m_1348_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1353_ = v_m_1348_;
v_isShared_1354_ = v_isSharedCheck_1401_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_buckets_1351_);
lean_inc(v_size_1350_);
lean_dec(v_m_1348_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1401_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; uint64_t v___x_1356_; uint64_t v___x_1357_; uint64_t v___x_1358_; uint64_t v_fold_1359_; uint64_t v___x_1360_; uint64_t v___x_1361_; uint64_t v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; size_t v___x_1365_; size_t v___x_1366_; size_t v___x_1367_; lean_object* v_bkt_1368_; uint8_t v___x_1369_; 
v___x_1355_ = lean_array_get_size(v_buckets_1351_);
v___x_1356_ = lean_string_hash(v_a_1349_);
v___x_1357_ = 32ULL;
v___x_1358_ = lean_uint64_shift_right(v___x_1356_, v___x_1357_);
v_fold_1359_ = lean_uint64_xor(v___x_1356_, v___x_1358_);
v___x_1360_ = 16ULL;
v___x_1361_ = lean_uint64_shift_right(v_fold_1359_, v___x_1360_);
v___x_1362_ = lean_uint64_xor(v_fold_1359_, v___x_1361_);
v___x_1363_ = lean_uint64_to_usize(v___x_1362_);
v___x_1364_ = lean_usize_of_nat(v___x_1355_);
v___x_1365_ = ((size_t)1ULL);
v___x_1366_ = lean_usize_sub(v___x_1364_, v___x_1365_);
v___x_1367_ = lean_usize_land(v___x_1363_, v___x_1366_);
v_bkt_1368_ = lean_array_uget_borrowed(v_buckets_1351_, v___x_1367_);
v___x_1369_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1349_, v_bkt_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v_size_x27_1373_; lean_object* v___x_1374_; lean_object* v_buckets_x27_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1370_ = lean_unsigned_to_nat(1u);
v___x_1371_ = lean_mk_empty_array_with_capacity(v___x_1370_);
v___x_1372_ = lean_array_push(v___x_1371_, v_i_1347_);
v_size_x27_1373_ = lean_nat_add(v_size_1350_, v___x_1370_);
lean_dec(v_size_1350_);
lean_inc(v_bkt_1368_);
v___x_1374_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1374_, 0, v_a_1349_);
lean_ctor_set(v___x_1374_, 1, v___x_1372_);
lean_ctor_set(v___x_1374_, 2, v_bkt_1368_);
v_buckets_x27_1375_ = lean_array_uset(v_buckets_1351_, v___x_1367_, v___x_1374_);
v___x_1376_ = lean_unsigned_to_nat(4u);
v___x_1377_ = lean_nat_mul(v_size_x27_1373_, v___x_1376_);
v___x_1378_ = lean_unsigned_to_nat(3u);
v___x_1379_ = lean_nat_div(v___x_1377_, v___x_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_array_get_size(v_buckets_x27_1375_);
v___x_1381_ = lean_nat_dec_le(v___x_1379_, v___x_1380_);
lean_dec(v___x_1379_);
if (v___x_1381_ == 0)
{
lean_object* v_val_1382_; lean_object* v___x_1384_; 
v_val_1382_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_buckets_x27_1375_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v_val_1382_);
lean_ctor_set(v___x_1353_, 0, v_size_x27_1373_);
v___x_1384_ = v___x_1353_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_size_x27_1373_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_val_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
else
{
lean_object* v___x_1387_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v_buckets_x27_1375_);
lean_ctor_set(v___x_1353_, 0, v_size_x27_1373_);
v___x_1387_ = v___x_1353_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_size_x27_1373_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_buckets_x27_1375_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
else
{
lean_object* v___x_1389_; lean_object* v_buckets_x27_1390_; lean_object* v_bkt_x27_1391_; lean_object* v___y_1393_; uint8_t v___x_1398_; 
lean_inc(v_bkt_1368_);
v___x_1389_ = lean_box(0);
v_buckets_x27_1390_ = lean_array_uset(v_buckets_1351_, v___x_1367_, v___x_1389_);
lean_inc_ref(v_a_1349_);
v_bkt_x27_1391_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_1347_, v_a_1349_, v_bkt_1368_);
v___x_1398_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1349_, v_bkt_x27_1391_);
lean_dec_ref(v_a_1349_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_unsigned_to_nat(1u);
v___x_1400_ = lean_nat_sub(v_size_1350_, v___x_1399_);
lean_dec(v_size_1350_);
v___y_1393_ = v___x_1400_;
goto v___jp_1392_;
}
else
{
v___y_1393_ = v_size_1350_;
goto v___jp_1392_;
}
v___jp_1392_:
{
lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1394_ = lean_array_uset(v_buckets_x27_1390_, v___x_1367_, v_bkt_x27_1391_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v___x_1394_);
lean_ctor_set(v___x_1353_, 0, v___y_1393_);
v___x_1396_ = v___x_1353_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___y_1393_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header(lean_object* v_builder_1402_, lean_object* v_key_1403_, lean_object* v_value_1404_){
_start:
{
lean_object* v_line_1405_; lean_object* v_headers_1406_; lean_object* v_extensions_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1438_; 
v_line_1405_ = lean_ctor_get(v_builder_1402_, 0);
lean_inc_ref(v_line_1405_);
v_headers_1406_ = lean_ctor_get(v_line_1405_, 1);
lean_inc_ref(v_headers_1406_);
v_extensions_1407_ = lean_ctor_get(v_builder_1402_, 1);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_builder_1402_);
if (v_isSharedCheck_1438_ == 0)
{
lean_object* v_unused_1439_; 
v_unused_1439_ = lean_ctor_get(v_builder_1402_, 0);
lean_dec(v_unused_1439_);
v___x_1409_ = v_builder_1402_;
v_isShared_1410_ = v_isSharedCheck_1438_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_extensions_1407_);
lean_dec(v_builder_1402_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1438_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
uint8_t v_method_1411_; uint8_t v_version_1412_; lean_object* v_uri_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1436_; 
v_method_1411_ = lean_ctor_get_uint8(v_line_1405_, sizeof(void*)*2);
v_version_1412_ = lean_ctor_get_uint8(v_line_1405_, sizeof(void*)*2 + 1);
v_uri_1413_ = lean_ctor_get(v_line_1405_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_line_1405_);
if (v_isSharedCheck_1436_ == 0)
{
lean_object* v_unused_1437_; 
v_unused_1437_ = lean_ctor_get(v_line_1405_, 1);
lean_dec(v_unused_1437_);
v___x_1415_ = v_line_1405_;
v_isShared_1416_ = v_isSharedCheck_1436_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_uri_1413_);
lean_dec(v_line_1405_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1436_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v_entries_1417_; lean_object* v_indexes_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1435_; 
v_entries_1417_ = lean_ctor_get(v_headers_1406_, 0);
v_indexes_1418_ = lean_ctor_get(v_headers_1406_, 1);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_headers_1406_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1420_ = v_headers_1406_;
v_isShared_1421_ = v_isSharedCheck_1435_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_indexes_1418_);
lean_inc(v_entries_1417_);
lean_dec(v_headers_1406_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1435_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v_i_1422_; lean_object* v___x_1423_; lean_object* v_entries_1424_; lean_object* v_indexes_1425_; lean_object* v___x_1427_; 
v_i_1422_ = lean_array_get_size(v_entries_1417_);
lean_inc_ref(v_key_1403_);
v___x_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1423_, 0, v_key_1403_);
lean_ctor_set(v___x_1423_, 1, v_value_1404_);
v_entries_1424_ = lean_array_push(v_entries_1417_, v___x_1423_);
v_indexes_1425_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1422_, v_indexes_1418_, v_key_1403_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 1, v_indexes_1425_);
lean_ctor_set(v___x_1420_, 0, v_entries_1424_);
v___x_1427_ = v___x_1420_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_entries_1424_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_indexes_1425_);
v___x_1427_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1429_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 1, v___x_1427_);
v___x_1429_ = v___x_1415_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_uri_1413_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v___x_1427_);
lean_ctor_set_uint8(v_reuseFailAlloc_1433_, sizeof(void*)*2, v_method_1411_);
lean_ctor_set_uint8(v_reuseFailAlloc_1433_, sizeof(void*)*2 + 1, v_version_1412_);
v___x_1429_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1431_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1429_);
v___x_1431_ = v___x_1409_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_extensions_1407_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(lean_object* v_00_u03b2_1440_, lean_object* v_a_1441_, lean_object* v_x_1442_){
_start:
{
uint8_t v___x_1443_; 
v___x_1443_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1441_, v_x_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1444_, lean_object* v_a_1445_, lean_object* v_x_1446_){
_start:
{
uint8_t v_res_1447_; lean_object* v_r_1448_; 
v_res_1447_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(v_00_u03b2_1444_, v_a_1445_, v_x_1446_);
lean_dec(v_x_1446_);
lean_dec_ref(v_a_1445_);
v_r_1448_ = lean_box(v_res_1447_);
return v_r_1448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1(lean_object* v_00_u03b2_1449_, lean_object* v_data_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_data_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1452_, lean_object* v_i_1453_, lean_object* v_source_1454_, lean_object* v_target_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v_i_1453_, v_source_1454_, v_target_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1457_, lean_object* v_x_1458_, lean_object* v_x_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1458_, v_x_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x21(lean_object* v_builder_1461_, lean_object* v_key_1462_, lean_object* v_value_1463_){
_start:
{
lean_object* v_line_1464_; lean_object* v_headers_1465_; lean_object* v_extensions_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1499_; 
v_line_1464_ = lean_ctor_get(v_builder_1461_, 0);
lean_inc_ref(v_line_1464_);
v_headers_1465_ = lean_ctor_get(v_line_1464_, 1);
lean_inc_ref(v_headers_1465_);
v_extensions_1466_ = lean_ctor_get(v_builder_1461_, 1);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_builder_1461_);
if (v_isSharedCheck_1499_ == 0)
{
lean_object* v_unused_1500_; 
v_unused_1500_ = lean_ctor_get(v_builder_1461_, 0);
lean_dec(v_unused_1500_);
v___x_1468_ = v_builder_1461_;
v_isShared_1469_ = v_isSharedCheck_1499_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_extensions_1466_);
lean_dec(v_builder_1461_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1499_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
uint8_t v_method_1470_; uint8_t v_version_1471_; lean_object* v_uri_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1497_; 
v_method_1470_ = lean_ctor_get_uint8(v_line_1464_, sizeof(void*)*2);
v_version_1471_ = lean_ctor_get_uint8(v_line_1464_, sizeof(void*)*2 + 1);
v_uri_1472_ = lean_ctor_get(v_line_1464_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_line_1464_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; 
v_unused_1498_ = lean_ctor_get(v_line_1464_, 1);
lean_dec(v_unused_1498_);
v___x_1474_ = v_line_1464_;
v_isShared_1475_ = v_isSharedCheck_1497_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_uri_1472_);
lean_dec(v_line_1464_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1497_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v_entries_1476_; lean_object* v_indexes_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1496_; 
v_entries_1476_ = lean_ctor_get(v_headers_1465_, 0);
v_indexes_1477_ = lean_ctor_get(v_headers_1465_, 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_headers_1465_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1479_ = v_headers_1465_;
v_isShared_1480_ = v_isSharedCheck_1496_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_indexes_1477_);
lean_inc(v_entries_1476_);
lean_dec(v_headers_1465_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1496_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v_key_1481_; lean_object* v_value_1482_; lean_object* v_i_1483_; lean_object* v___x_1484_; lean_object* v_entries_1485_; lean_object* v_indexes_1486_; lean_object* v___x_1488_; 
v_key_1481_ = l_Std_Http_Header_Name_ofString_x21(v_key_1462_);
v_value_1482_ = l_Std_Http_Header_Value_ofString_x21(v_value_1463_);
v_i_1483_ = lean_array_get_size(v_entries_1476_);
lean_inc_ref(v_key_1481_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_key_1481_);
lean_ctor_set(v___x_1484_, 1, v_value_1482_);
v_entries_1485_ = lean_array_push(v_entries_1476_, v___x_1484_);
v_indexes_1486_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1483_, v_indexes_1477_, v_key_1481_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 1, v_indexes_1486_);
lean_ctor_set(v___x_1479_, 0, v_entries_1485_);
v___x_1488_ = v___x_1479_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_entries_1485_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_indexes_1486_);
v___x_1488_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1490_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 1, v___x_1488_);
v___x_1490_ = v___x_1474_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_uri_1472_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v___x_1488_);
lean_ctor_set_uint8(v_reuseFailAlloc_1494_, sizeof(void*)*2, v_method_1470_);
lean_ctor_set_uint8(v_reuseFailAlloc_1494_, sizeof(void*)*2 + 1, v_version_1471_);
v___x_1490_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1492_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1490_);
v___x_1492_ = v___x_1468_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_extensions_1466_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x3f(lean_object* v_builder_1501_, lean_object* v_key_1502_, lean_object* v_value_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Std_Http_Header_Name_ofString_x3f(v_key_1502_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v___x_1505_; 
lean_dec_ref(v_value_1503_);
lean_dec_ref(v_builder_1501_);
v___x_1505_ = lean_box(0);
return v___x_1505_;
}
else
{
lean_object* v_val_1506_; lean_object* v___x_1507_; 
v_val_1506_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_val_1506_);
lean_dec_ref_known(v___x_1504_, 1);
v___x_1507_ = l_Std_Http_Header_Value_ofString_x3f(v_value_1503_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v___x_1508_; 
lean_dec(v_val_1506_);
lean_dec_ref(v_builder_1501_);
v___x_1508_ = lean_box(0);
return v___x_1508_;
}
else
{
lean_object* v_line_1509_; lean_object* v_headers_1510_; lean_object* v_val_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1551_; 
v_line_1509_ = lean_ctor_get(v_builder_1501_, 0);
lean_inc_ref(v_line_1509_);
v_headers_1510_ = lean_ctor_get(v_line_1509_, 1);
lean_inc_ref(v_headers_1510_);
v_val_1511_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1513_ = v___x_1507_;
v_isShared_1514_ = v_isSharedCheck_1551_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_val_1511_);
lean_dec(v___x_1507_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1551_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v_extensions_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1549_; 
v_extensions_1515_ = lean_ctor_get(v_builder_1501_, 1);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_builder_1501_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v_builder_1501_, 0);
lean_dec(v_unused_1550_);
v___x_1517_ = v_builder_1501_;
v_isShared_1518_ = v_isSharedCheck_1549_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_extensions_1515_);
lean_dec(v_builder_1501_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1549_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
uint8_t v_method_1519_; uint8_t v_version_1520_; lean_object* v_uri_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1547_; 
v_method_1519_ = lean_ctor_get_uint8(v_line_1509_, sizeof(void*)*2);
v_version_1520_ = lean_ctor_get_uint8(v_line_1509_, sizeof(void*)*2 + 1);
v_uri_1521_ = lean_ctor_get(v_line_1509_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_line_1509_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v_line_1509_, 1);
lean_dec(v_unused_1548_);
v___x_1523_ = v_line_1509_;
v_isShared_1524_ = v_isSharedCheck_1547_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_uri_1521_);
lean_dec(v_line_1509_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1547_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v_entries_1525_; lean_object* v_indexes_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1546_; 
v_entries_1525_ = lean_ctor_get(v_headers_1510_, 0);
v_indexes_1526_ = lean_ctor_get(v_headers_1510_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_headers_1510_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1528_ = v_headers_1510_;
v_isShared_1529_ = v_isSharedCheck_1546_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_indexes_1526_);
lean_inc(v_entries_1525_);
lean_dec(v_headers_1510_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1546_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v_i_1530_; lean_object* v___x_1531_; lean_object* v_entries_1532_; lean_object* v_indexes_1533_; lean_object* v___x_1535_; 
v_i_1530_ = lean_array_get_size(v_entries_1525_);
lean_inc(v_val_1506_);
v___x_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1531_, 0, v_val_1506_);
lean_ctor_set(v___x_1531_, 1, v_val_1511_);
v_entries_1532_ = lean_array_push(v_entries_1525_, v___x_1531_);
v_indexes_1533_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1530_, v_indexes_1526_, v_val_1506_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 1, v_indexes_1533_);
lean_ctor_set(v___x_1528_, 0, v_entries_1532_);
v___x_1535_ = v___x_1528_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_entries_1532_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_indexes_1533_);
v___x_1535_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1537_; 
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 1, v___x_1535_);
v___x_1537_ = v___x_1523_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_uri_1521_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v___x_1535_);
lean_ctor_set_uint8(v_reuseFailAlloc_1544_, sizeof(void*)*2, v_method_1519_);
lean_ctor_set_uint8(v_reuseFailAlloc_1544_, sizeof(void*)*2 + 1, v_version_1520_);
v___x_1537_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1539_; 
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1537_);
v___x_1539_ = v___x_1517_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_extensions_1515_);
v___x_1539_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
lean_object* v___x_1541_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1539_);
v___x_1541_ = v___x_1513_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
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
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headerOpt(lean_object* v_builder_1552_, lean_object* v_key_1553_, lean_object* v_value_1554_){
_start:
{
if (lean_obj_tag(v_value_1554_) == 0)
{
lean_dec_ref(v_key_1553_);
return v_builder_1552_;
}
else
{
lean_object* v_val_1555_; lean_object* v___x_1556_; 
v_val_1555_ = lean_ctor_get(v_value_1554_, 0);
lean_inc(v_val_1555_);
lean_dec_ref_known(v_value_1554_, 1);
v___x_1556_ = l_Std_Http_Request_Builder_header(v_builder_1552_, v_key_1553_, v_val_1555_);
return v___x_1556_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension___redArg(lean_object* v_builder_1558_, lean_object* v_inst_1559_, lean_object* v_data_1560_){
_start:
{
lean_object* v_line_1561_; lean_object* v_extensions_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1573_; 
v_line_1561_ = lean_ctor_get(v_builder_1558_, 0);
v_extensions_1562_ = lean_ctor_get(v_builder_1558_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_builder_1558_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1564_ = v_builder_1558_;
v_isShared_1565_ = v_isSharedCheck_1573_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_extensions_1562_);
lean_inc(v_line_1561_);
lean_dec(v_builder_1558_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1573_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v_dyn_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v_dyn_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_1566_, 0, v_inst_1559_);
lean_ctor_set(v_dyn_1566_, 1, v_data_1560_);
v___x_1567_ = ((lean_object*)(l_Std_Http_Request_Builder_extension___redArg___closed__0));
v___x_1568_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_1566_);
v___x_1569_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1567_, v___x_1568_, v_dyn_1566_, v_extensions_1562_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 1, v___x_1569_);
v___x_1571_ = v___x_1564_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_line_1561_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension(lean_object* v_00_u03b1_1574_, lean_object* v_builder_1575_, lean_object* v_inst_1576_, lean_object* v_data_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Std_Http_Request_Builder_extension___redArg(v_builder_1575_, v_inst_1576_, v_data_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object* v_builder_1579_, lean_object* v_body_1580_){
_start:
{
lean_object* v_line_1581_; lean_object* v_extensions_1582_; lean_object* v___x_1583_; 
v_line_1581_ = lean_ctor_get(v_builder_1579_, 0);
v_extensions_1582_ = lean_ctor_get(v_builder_1579_, 1);
lean_inc(v_extensions_1582_);
lean_inc_ref(v_line_1581_);
v___x_1583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1583_, 0, v_line_1581_);
lean_ctor_set(v___x_1583_, 1, v_body_1580_);
lean_ctor_set(v___x_1583_, 2, v_extensions_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg___boxed(lean_object* v_builder_1584_, lean_object* v_body_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1584_, v_body_1585_);
lean_dec_ref(v_builder_1584_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body(lean_object* v_t_1587_, lean_object* v_builder_1588_, lean_object* v_body_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1588_, v_body_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___boxed(lean_object* v_t_1591_, lean_object* v_builder_1592_, lean_object* v_body_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Std_Http_Request_Builder_body(v_t_1591_, v_builder_1592_, v_body_1593_);
lean_dec_ref(v_builder_1592_);
return v_res_1594_;
}
}
static lean_object* _init_l_Std_Http_Request_get___closed__0(void){
_start:
{
uint8_t v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1595_ = 8;
v___x_1596_ = l_Std_Http_Request_new;
v___x_1597_ = l_Std_Http_Request_Builder_method(v___x_1596_, v___x_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_get(lean_object* v_uri_1598_){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = lean_obj_once(&l_Std_Http_Request_get___closed__0, &l_Std_Http_Request_get___closed__0_once, _init_l_Std_Http_Request_get___closed__0);
v___x_1600_ = l_Std_Http_Request_Builder_uri(v___x_1599_, v_uri_1598_);
return v___x_1600_;
}
}
static lean_object* _init_l_Std_Http_Request_post___closed__0(void){
_start:
{
uint8_t v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1601_ = 23;
v___x_1602_ = l_Std_Http_Request_new;
v___x_1603_ = l_Std_Http_Request_Builder_method(v___x_1602_, v___x_1601_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_post(lean_object* v_uri_1604_){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_obj_once(&l_Std_Http_Request_post___closed__0, &l_Std_Http_Request_post___closed__0_once, _init_l_Std_Http_Request_post___closed__0);
v___x_1606_ = l_Std_Http_Request_Builder_uri(v___x_1605_, v_uri_1604_);
return v___x_1606_;
}
}
static lean_object* _init_l_Std_Http_Request_put___closed__0(void){
_start:
{
uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1607_ = 27;
v___x_1608_ = l_Std_Http_Request_new;
v___x_1609_ = l_Std_Http_Request_Builder_method(v___x_1608_, v___x_1607_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_put(lean_object* v_uri_1610_){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_obj_once(&l_Std_Http_Request_put___closed__0, &l_Std_Http_Request_put___closed__0_once, _init_l_Std_Http_Request_put___closed__0);
v___x_1612_ = l_Std_Http_Request_Builder_uri(v___x_1611_, v_uri_1610_);
return v___x_1612_;
}
}
static lean_object* _init_l_Std_Http_Request_delete___closed__0(void){
_start:
{
uint8_t v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1613_ = 7;
v___x_1614_ = l_Std_Http_Request_new;
v___x_1615_ = l_Std_Http_Request_Builder_method(v___x_1614_, v___x_1613_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_delete(lean_object* v_uri_1616_){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_obj_once(&l_Std_Http_Request_delete___closed__0, &l_Std_Http_Request_delete___closed__0_once, _init_l_Std_Http_Request_delete___closed__0);
v___x_1618_ = l_Std_Http_Request_Builder_uri(v___x_1617_, v_uri_1616_);
return v___x_1618_;
}
}
static lean_object* _init_l_Std_Http_Request_patch___closed__0(void){
_start:
{
uint8_t v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1619_ = 22;
v___x_1620_ = l_Std_Http_Request_new;
v___x_1621_ = l_Std_Http_Request_Builder_method(v___x_1620_, v___x_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_patch(lean_object* v_uri_1622_){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_obj_once(&l_Std_Http_Request_patch___closed__0, &l_Std_Http_Request_patch___closed__0_once, _init_l_Std_Http_Request_patch___closed__0);
v___x_1624_ = l_Std_Http_Request_Builder_uri(v___x_1623_, v_uri_1622_);
return v___x_1624_;
}
}
static lean_object* _init_l_Std_Http_Request_head___closed__0(void){
_start:
{
uint8_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1625_ = 9;
v___x_1626_ = l_Std_Http_Request_new;
v___x_1627_ = l_Std_Http_Request_Builder_method(v___x_1626_, v___x_1625_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_head(lean_object* v_uri_1628_){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_obj_once(&l_Std_Http_Request_head___closed__0, &l_Std_Http_Request_head___closed__0_once, _init_l_Std_Http_Request_head___closed__0);
v___x_1630_ = l_Std_Http_Request_Builder_uri(v___x_1629_, v_uri_1628_);
return v___x_1630_;
}
}
static lean_object* _init_l_Std_Http_Request_options___closed__0(void){
_start:
{
uint8_t v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = 20;
v___x_1632_ = l_Std_Http_Request_new;
v___x_1633_ = l_Std_Http_Request_Builder_method(v___x_1632_, v___x_1631_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_options(lean_object* v_uri_1634_){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = lean_obj_once(&l_Std_Http_Request_options___closed__0, &l_Std_Http_Request_options___closed__0_once, _init_l_Std_Http_Request_options___closed__0);
v___x_1636_ = l_Std_Http_Request_Builder_uri(v___x_1635_, v_uri_1634_);
return v___x_1636_;
}
}
static lean_object* _init_l_Std_Http_Request_connect___closed__0(void){
_start:
{
uint8_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1637_ = 5;
v___x_1638_ = l_Std_Http_Request_new;
v___x_1639_ = l_Std_Http_Request_Builder_method(v___x_1638_, v___x_1637_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_connect(lean_object* v_uri_1640_){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = lean_obj_once(&l_Std_Http_Request_connect___closed__0, &l_Std_Http_Request_connect___closed__0_once, _init_l_Std_Http_Request_connect___closed__0);
v___x_1642_ = l_Std_Http_Request_Builder_uri(v___x_1641_, v_uri_1640_);
return v___x_1642_;
}
}
static lean_object* _init_l_Std_Http_Request_trace___closed__0(void){
_start:
{
uint8_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1643_ = 32;
v___x_1644_ = l_Std_Http_Request_new;
v___x_1645_ = l_Std_Http_Request_Builder_method(v___x_1644_, v___x_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_trace(lean_object* v_uri_1646_){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_obj_once(&l_Std_Http_Request_trace___closed__0, &l_Std_Http_Request_trace___closed__0_once, _init_l_Std_Http_Request_trace___closed__0);
v___x_1648_ = l_Std_Http_Request_Builder_uri(v___x_1647_, v_uri_1646_);
return v___x_1648_;
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
