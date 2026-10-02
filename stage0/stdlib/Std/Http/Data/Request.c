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
lean_object* v_it_136_; lean_object* v_out_137_; lean_object* v___y_153_; lean_object* v___y_154_; uint32_t v___y_155_; uint8_t v___y_156_; lean_object* v_it_162_; lean_object* v_startInclusive_163_; lean_object* v_endExclusive_164_; 
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
v___x_157_ = lean_string_utf8_set(v___y_153_, v___x_125_, v___y_155_);
v_it_136_ = v___y_154_;
v_out_137_ = v___x_157_;
goto v___jp_135_;
}
else
{
uint32_t v___x_158_; uint32_t v___x_159_; lean_object* v___x_160_; 
v___x_158_ = 4294967264;
v___x_159_ = lean_uint32_add(v___y_155_, v___x_158_);
v___x_160_ = lean_string_utf8_set(v___y_153_, v___x_125_, v___x_159_);
v_it_136_ = v___y_154_;
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
v___y_154_ = v_it_162_;
v___y_155_ = v___x_166_;
v___y_156_ = v___x_168_;
goto v___jp_152_;
}
else
{
uint32_t v___x_169_; uint8_t v___x_170_; 
v___x_169_ = 122;
v___x_170_ = lean_uint32_dec_le(v___x_166_, v___x_169_);
v___y_153_ = v___x_165_;
v___y_154_ = v_it_162_;
v___y_155_ = v___x_166_;
v___y_156_ = v___x_170_;
goto v___jp_152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__1___boxed(lean_object* v___x_195_, lean_object* v___x_196_, lean_object* v___x_197_, lean_object* v_fst_198_, lean_object* v___x_199_, lean_object* v___x_200_, lean_object* v___x_201_, lean_object* v_it_202_, lean_object* v_acc_203_, lean_object* v_hP_204_, lean_object* v_recur_205_){
_start:
{
uint32_t v___x_1560__boxed_206_; lean_object* v_res_207_; 
v___x_1560__boxed_206_ = lean_unbox_uint32(v___x_200_);
lean_dec(v___x_200_);
v_res_207_ = l_Std_Http_Request_instToStringHead___lam__1(v___x_195_, v___x_196_, v___x_197_, v_fst_198_, v___x_199_, v___x_1560__boxed_206_, v___x_201_, v_it_202_, v_acc_203_, v_hP_204_, v_recur_205_);
lean_dec_ref(v___x_201_);
lean_dec_ref(v_fst_198_);
lean_dec(v___x_197_);
lean_dec(v___x_196_);
lean_dec_ref(v___x_195_);
return v_res_207_;
}
}
static lean_object* _init_l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1(void){
_start:
{
uint32_t v___x_212_; lean_object* v___x_213_; 
v___x_212_ = 45;
v___x_213_ = lean_box_uint32(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2(lean_object* v_x_214_){
_start:
{
lean_object* v_fst_215_; lean_object* v_snd_216_; lean_object* v___y_218_; lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_it_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___f_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_fst_215_ = lean_ctor_get(v_x_214_, 0);
lean_inc_n(v_fst_215_, 2);
v_snd_216_ = lean_ctor_get(v_x_214_, 1);
lean_inc(v_snd_216_);
lean_dec_ref(v_x_214_);
v___f_222_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__1));
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = lean_string_utf8_byte_size(v_fst_215_);
v___x_225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_225_, 0, v_fst_215_);
lean_ctor_set(v___x_225_, 1, v___x_223_);
lean_ctor_set(v___x_225_, 2, v___x_224_);
lean_inc_ref(v___x_225_);
v_it_226_ = l_String_Slice_splitToSubslice___redArg(v___x_225_, v___f_222_);
v___x_227_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__2));
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1;
v___f_230_ = lean_alloc_closure((void*)(l_Std_Http_Request_instToStringHead___lam__1___boxed), 11, 7);
lean_closure_set(v___f_230_, 0, v___x_227_);
lean_closure_set(v___f_230_, 1, v___x_223_);
lean_closure_set(v___f_230_, 2, v___x_228_);
lean_closure_set(v___f_230_, 3, v_fst_215_);
lean_closure_set(v___f_230_, 4, v___x_224_);
lean_closure_set(v___f_230_, 5, v___x_229_);
lean_closure_set(v___f_230_, 6, v___x_225_);
v___x_231_ = lean_box(0);
v___x_232_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_230_, v_it_226_, v___x_231_, lean_box(0));
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v___x_233_; 
v___x_233_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_218_ = v___x_233_;
goto v___jp_217_;
}
else
{
lean_object* v_val_234_; 
v_val_234_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_232_, 1);
v___y_218_ = v_val_234_;
goto v___jp_217_;
}
v___jp_217_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__0));
v___x_220_ = lean_string_append(v___y_218_, v___x_219_);
v___x_221_ = lean_string_append(v___x_220_, v_snd_216_);
lean_dec(v_snd_216_);
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__4(lean_object* v___f_308_, lean_object* v___f_309_, lean_object* v___f_310_, lean_object* v_req_311_){
_start:
{
uint8_t v_method_312_; uint8_t v_version_313_; lean_object* v_uri_314_; lean_object* v_headers_315_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v_port_418_; lean_object* v___y_419_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v_host_435_; lean_object* v_port_436_; lean_object* v___y_437_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v_port_459_; lean_object* v___y_460_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v_host_471_; lean_object* v_port_472_; lean_object* v___y_473_; lean_object* v___y_484_; 
v_method_312_ = lean_ctor_get_uint8(v_req_311_, sizeof(void*)*2);
v_version_313_ = lean_ctor_get_uint8(v_req_311_, sizeof(void*)*2 + 1);
v_uri_314_ = lean_ctor_get(v_req_311_, 0);
lean_inc(v_uri_314_);
v_headers_315_ = lean_ctor_get(v_req_311_, 1);
lean_inc_ref(v_headers_315_);
lean_dec_ref(v_req_311_);
switch(v_method_312_)
{
case 0:
{
lean_object* v___x_556_; 
v___x_556_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__24));
v___y_484_ = v___x_556_;
goto v___jp_483_;
}
case 1:
{
lean_object* v___x_557_; 
v___x_557_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__25));
v___y_484_ = v___x_557_;
goto v___jp_483_;
}
case 2:
{
lean_object* v___x_558_; 
v___x_558_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__26));
v___y_484_ = v___x_558_;
goto v___jp_483_;
}
case 3:
{
lean_object* v___x_559_; 
v___x_559_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__27));
v___y_484_ = v___x_559_;
goto v___jp_483_;
}
case 4:
{
lean_object* v___x_560_; 
v___x_560_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__28));
v___y_484_ = v___x_560_;
goto v___jp_483_;
}
case 5:
{
lean_object* v___x_561_; 
v___x_561_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__29));
v___y_484_ = v___x_561_;
goto v___jp_483_;
}
case 6:
{
lean_object* v___x_562_; 
v___x_562_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__30));
v___y_484_ = v___x_562_;
goto v___jp_483_;
}
case 7:
{
lean_object* v___x_563_; 
v___x_563_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__31));
v___y_484_ = v___x_563_;
goto v___jp_483_;
}
case 8:
{
lean_object* v___x_564_; 
v___x_564_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__32));
v___y_484_ = v___x_564_;
goto v___jp_483_;
}
case 9:
{
lean_object* v___x_565_; 
v___x_565_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__33));
v___y_484_ = v___x_565_;
goto v___jp_483_;
}
case 10:
{
lean_object* v___x_566_; 
v___x_566_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__34));
v___y_484_ = v___x_566_;
goto v___jp_483_;
}
case 11:
{
lean_object* v___x_567_; 
v___x_567_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__35));
v___y_484_ = v___x_567_;
goto v___jp_483_;
}
case 12:
{
lean_object* v___x_568_; 
v___x_568_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__36));
v___y_484_ = v___x_568_;
goto v___jp_483_;
}
case 13:
{
lean_object* v___x_569_; 
v___x_569_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__37));
v___y_484_ = v___x_569_;
goto v___jp_483_;
}
case 14:
{
lean_object* v___x_570_; 
v___x_570_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__38));
v___y_484_ = v___x_570_;
goto v___jp_483_;
}
case 15:
{
lean_object* v___x_571_; 
v___x_571_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__39));
v___y_484_ = v___x_571_;
goto v___jp_483_;
}
case 16:
{
lean_object* v___x_572_; 
v___x_572_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__40));
v___y_484_ = v___x_572_;
goto v___jp_483_;
}
case 17:
{
lean_object* v___x_573_; 
v___x_573_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__41));
v___y_484_ = v___x_573_;
goto v___jp_483_;
}
case 18:
{
lean_object* v___x_574_; 
v___x_574_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__42));
v___y_484_ = v___x_574_;
goto v___jp_483_;
}
case 19:
{
lean_object* v___x_575_; 
v___x_575_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__43));
v___y_484_ = v___x_575_;
goto v___jp_483_;
}
case 20:
{
lean_object* v___x_576_; 
v___x_576_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__44));
v___y_484_ = v___x_576_;
goto v___jp_483_;
}
case 21:
{
lean_object* v___x_577_; 
v___x_577_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__45));
v___y_484_ = v___x_577_;
goto v___jp_483_;
}
case 22:
{
lean_object* v___x_578_; 
v___x_578_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__46));
v___y_484_ = v___x_578_;
goto v___jp_483_;
}
case 23:
{
lean_object* v___x_579_; 
v___x_579_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__47));
v___y_484_ = v___x_579_;
goto v___jp_483_;
}
case 24:
{
lean_object* v___x_580_; 
v___x_580_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__48));
v___y_484_ = v___x_580_;
goto v___jp_483_;
}
case 25:
{
lean_object* v___x_581_; 
v___x_581_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__49));
v___y_484_ = v___x_581_;
goto v___jp_483_;
}
case 26:
{
lean_object* v___x_582_; 
v___x_582_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__50));
v___y_484_ = v___x_582_;
goto v___jp_483_;
}
case 27:
{
lean_object* v___x_583_; 
v___x_583_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__51));
v___y_484_ = v___x_583_;
goto v___jp_483_;
}
case 28:
{
lean_object* v___x_584_; 
v___x_584_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__52));
v___y_484_ = v___x_584_;
goto v___jp_483_;
}
case 29:
{
lean_object* v___x_585_; 
v___x_585_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__53));
v___y_484_ = v___x_585_;
goto v___jp_483_;
}
case 30:
{
lean_object* v___x_586_; 
v___x_586_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__54));
v___y_484_ = v___x_586_;
goto v___jp_483_;
}
case 31:
{
lean_object* v___x_587_; 
v___x_587_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__55));
v___y_484_ = v___x_587_;
goto v___jp_483_;
}
case 32:
{
lean_object* v___x_588_; 
v___x_588_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__56));
v___y_484_ = v___x_588_;
goto v___jp_483_;
}
case 33:
{
lean_object* v___x_589_; 
v___x_589_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__57));
v___y_484_ = v___x_589_;
goto v___jp_483_;
}
case 34:
{
lean_object* v___x_590_; 
v___x_590_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__58));
v___y_484_ = v___x_590_;
goto v___jp_483_;
}
case 35:
{
lean_object* v___x_591_; 
v___x_591_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__59));
v___y_484_ = v___x_591_;
goto v___jp_483_;
}
case 36:
{
lean_object* v___x_592_; 
v___x_592_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__60));
v___y_484_ = v___x_592_;
goto v___jp_483_;
}
case 37:
{
lean_object* v___x_593_; 
v___x_593_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__61));
v___y_484_ = v___x_593_;
goto v___jp_483_;
}
case 38:
{
lean_object* v___x_594_; 
v___x_594_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__62));
v___y_484_ = v___x_594_;
goto v___jp_483_;
}
default: 
{
lean_object* v___x_595_; 
v___x_595_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__63));
v___y_484_ = v___x_595_;
goto v___jp_483_;
}
}
v___jp_316_:
{
lean_object* v_entries_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; size_t v_sz_324_; size_t v___x_325_; lean_object* v_pairs_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_entries_319_ = lean_ctor_get(v_headers_315_, 0);
lean_inc_ref(v_entries_319_);
lean_dec_ref(v_headers_315_);
v___x_320_ = lean_string_append(v___y_317_, v___y_318_);
v___x_321_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__0));
v___x_322_ = lean_string_append(v___x_320_, v___x_321_);
v___x_323_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_324_ = lean_array_size(v_entries_319_);
v___x_325_ = ((size_t)0ULL);
v_pairs_326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_323_, v___f_308_, v_sz_324_, v___x_325_, v_entries_319_);
v___x_327_ = lean_array_to_list(v_pairs_326_);
v___x_328_ = l_String_intercalate(v___x_321_, v___x_327_);
v___x_329_ = lean_string_append(v___x_322_, v___x_328_);
lean_dec_ref(v___x_328_);
v___x_330_ = lean_string_append(v___x_329_, v___x_321_);
return v___x_330_;
}
v___jp_331_:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_string_append(v___y_332_, v___y_334_);
lean_dec_ref(v___y_334_);
v___x_336_ = lean_string_append(v___x_335_, v___y_333_);
switch(v_version_313_)
{
case 0:
{
lean_object* v___x_337_; 
v___x_337_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__11));
v___y_317_ = v___x_336_;
v___y_318_ = v___x_337_;
goto v___jp_316_;
}
case 1:
{
lean_object* v___x_338_; 
v___x_338_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__12));
v___y_317_ = v___x_336_;
v___y_318_ = v___x_338_;
goto v___jp_316_;
}
case 2:
{
lean_object* v___x_339_; 
v___x_339_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__13));
v___y_317_ = v___x_336_;
v___y_318_ = v___x_339_;
goto v___jp_316_;
}
default: 
{
lean_object* v___x_340_; 
v___x_340_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__14));
v___y_317_ = v___x_336_;
v___y_318_ = v___x_340_;
goto v___jp_316_;
}
}
}
v___jp_341_:
{
lean_object* v_queryStr_346_; lean_object* v___x_347_; 
v_queryStr_346_ = l_Std_Http_URI_Query_formatOption(v___y_344_);
v___x_347_ = lean_string_append(v___y_345_, v_queryStr_346_);
lean_dec_ref(v_queryStr_346_);
v___y_332_ = v___y_342_;
v___y_333_ = v___y_343_;
v___y_334_ = v___x_347_;
goto v___jp_331_;
}
v___jp_348_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_356_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_357_ = lean_string_append(v___y_349_, v___x_356_);
v___x_358_ = lean_string_append(v___x_357_, v___y_352_);
lean_dec_ref(v___y_352_);
v___x_359_ = lean_string_append(v___x_358_, v___y_353_);
lean_dec_ref(v___y_353_);
v___x_360_ = lean_string_append(v___x_359_, v___y_354_);
lean_dec_ref(v___y_354_);
v___x_361_ = lean_string_append(v___x_360_, v___y_355_);
lean_dec_ref(v___y_355_);
v___y_332_ = v___y_350_;
v___y_333_ = v___y_351_;
v___y_334_ = v___x_361_;
goto v___jp_331_;
}
v___jp_362_:
{
lean_object* v_queryPart_370_; 
v_queryPart_370_ = l_Std_Http_URI_Query_formatOption(v___y_365_);
if (lean_obj_tag(v___y_363_) == 0)
{
lean_object* v___x_371_; 
v___x_371_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_349_ = v___y_364_;
v___y_350_ = v___y_366_;
v___y_351_ = v___y_367_;
v___y_352_ = v___y_368_;
v___y_353_ = v___y_369_;
v___y_354_ = v_queryPart_370_;
v___y_355_ = v___x_371_;
goto v___jp_348_;
}
else
{
lean_object* v_val_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_val_372_ = lean_ctor_get(v___y_363_, 0);
lean_inc(v_val_372_);
lean_dec_ref_known(v___y_363_, 1);
v___x_373_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__16));
v___x_374_ = l_Std_Http_URI_EncodedFragment_encode(v_val_372_);
lean_dec(v_val_372_);
v___x_375_ = lean_string_from_utf8_unchecked(v___x_374_);
v___x_376_ = lean_string_append(v___x_373_, v___x_375_);
lean_dec_ref(v___x_375_);
v___y_349_ = v___y_364_;
v___y_350_ = v___y_366_;
v___y_351_ = v___y_367_;
v___y_352_ = v___y_368_;
v___y_353_ = v___y_369_;
v___y_354_ = v_queryPart_370_;
v___y_355_ = v___x_376_;
goto v___jp_348_;
}
}
v___jp_377_:
{
lean_object* v_segments_385_; uint8_t v_absolute_386_; lean_object* v___x_387_; lean_object* v___x_388_; size_t v_sz_389_; size_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_result_393_; 
v_segments_385_ = lean_ctor_get(v___y_378_, 0);
lean_inc_ref(v_segments_385_);
v_absolute_386_ = lean_ctor_get_uint8(v___y_378_, sizeof(void*)*1);
lean_dec_ref(v___y_378_);
v___x_387_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_388_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_389_ = lean_array_size(v_segments_385_);
v___x_390_ = ((size_t)0ULL);
v___x_391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_388_, v___f_309_, v_sz_389_, v___x_390_, v_segments_385_);
v___x_392_ = lean_array_to_list(v___x_391_);
v_result_393_ = l_String_intercalate(v___x_387_, v___x_392_);
if (v_absolute_386_ == 0)
{
v___y_363_ = v___y_381_;
v___y_364_ = v___y_380_;
v___y_365_ = v___y_379_;
v___y_366_ = v___y_382_;
v___y_367_ = v___y_383_;
v___y_368_ = v___y_384_;
v___y_369_ = v_result_393_;
goto v___jp_362_;
}
else
{
lean_object* v___x_394_; 
v___x_394_ = lean_string_append(v___x_387_, v_result_393_);
lean_dec_ref(v_result_393_);
v___y_363_ = v___y_381_;
v___y_364_ = v___y_380_;
v___y_365_ = v___y_379_;
v___y_366_ = v___y_382_;
v___y_367_ = v___y_383_;
v___y_368_ = v___y_384_;
v___y_369_ = v___x_394_;
goto v___jp_362_;
}
}
v___jp_395_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_string_append(v___y_403_, v___y_401_);
lean_dec_ref(v___y_401_);
v___x_407_ = lean_string_append(v___x_406_, v___y_405_);
lean_dec_ref(v___y_405_);
lean_inc_ref(v___y_400_);
v___x_408_ = lean_string_append(v___y_400_, v___x_407_);
lean_dec_ref(v___x_407_);
v___y_378_ = v___y_396_;
v___y_379_ = v___y_399_;
v___y_380_ = v___y_398_;
v___y_381_ = v___y_397_;
v___y_382_ = v___y_402_;
v___y_383_ = v___y_404_;
v___y_384_ = v___x_408_;
goto v___jp_377_;
}
v___jp_409_:
{
switch(lean_obj_tag(v_port_418_))
{
case 0:
{
lean_object* v___x_420_; 
v___x_420_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_396_ = v___y_410_;
v___y_397_ = v___y_413_;
v___y_398_ = v___y_412_;
v___y_399_ = v___y_411_;
v___y_400_ = v___y_414_;
v___y_401_ = v___y_419_;
v___y_402_ = v___y_416_;
v___y_403_ = v___y_415_;
v___y_404_ = v___y_417_;
v___y_405_ = v___x_420_;
goto v___jp_395_;
}
case 1:
{
lean_object* v___x_421_; 
v___x_421_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_396_ = v___y_410_;
v___y_397_ = v___y_413_;
v___y_398_ = v___y_412_;
v___y_399_ = v___y_411_;
v___y_400_ = v___y_414_;
v___y_401_ = v___y_419_;
v___y_402_ = v___y_416_;
v___y_403_ = v___y_415_;
v___y_404_ = v___y_417_;
v___y_405_ = v___x_421_;
goto v___jp_395_;
}
default: 
{
uint16_t v_port_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_port_422_ = lean_ctor_get_uint16(v_port_418_, 0);
lean_dec_ref_known(v_port_418_, 0);
v___x_423_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_424_ = lean_uint16_to_nat(v_port_422_);
v___x_425_ = l_Nat_reprFast(v___x_424_);
v___x_426_ = lean_string_append(v___x_423_, v___x_425_);
lean_dec_ref(v___x_425_);
v___y_396_ = v___y_410_;
v___y_397_ = v___y_413_;
v___y_398_ = v___y_412_;
v___y_399_ = v___y_411_;
v___y_400_ = v___y_414_;
v___y_401_ = v___y_419_;
v___y_402_ = v___y_416_;
v___y_403_ = v___y_415_;
v___y_404_ = v___y_417_;
v___y_405_ = v___x_426_;
goto v___jp_395_;
}
}
}
v___jp_427_:
{
switch(lean_obj_tag(v_host_435_))
{
case 0:
{
lean_object* v_name_438_; 
v_name_438_ = lean_ctor_get(v_host_435_, 0);
lean_inc_ref(v_name_438_);
lean_dec_ref_known(v_host_435_, 1);
v___y_410_ = v___y_428_;
v___y_411_ = v___y_431_;
v___y_412_ = v___y_430_;
v___y_413_ = v___y_429_;
v___y_414_ = v___y_432_;
v___y_415_ = v___y_437_;
v___y_416_ = v___y_433_;
v___y_417_ = v___y_434_;
v_port_418_ = v_port_436_;
v___y_419_ = v_name_438_;
goto v___jp_409_;
}
case 1:
{
lean_object* v_ipv4_439_; lean_object* v___x_440_; 
v_ipv4_439_ = lean_ctor_get(v_host_435_, 0);
lean_inc_ref(v_ipv4_439_);
lean_dec_ref_known(v_host_435_, 1);
v___x_440_ = lean_uv_ntop_v4(v_ipv4_439_);
lean_dec_ref(v_ipv4_439_);
v___y_410_ = v___y_428_;
v___y_411_ = v___y_431_;
v___y_412_ = v___y_430_;
v___y_413_ = v___y_429_;
v___y_414_ = v___y_432_;
v___y_415_ = v___y_437_;
v___y_416_ = v___y_433_;
v___y_417_ = v___y_434_;
v_port_418_ = v_port_436_;
v___y_419_ = v___x_440_;
goto v___jp_409_;
}
default: 
{
lean_object* v_ipv6_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_ipv6_441_ = lean_ctor_get(v_host_435_, 0);
lean_inc_ref(v_ipv6_441_);
lean_dec_ref_known(v_host_435_, 1);
v___x_442_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_443_ = lean_uv_ntop_v6(v_ipv6_441_);
lean_dec_ref(v_ipv6_441_);
v___x_444_ = lean_string_append(v___x_442_, v___x_443_);
lean_dec_ref(v___x_443_);
v___x_445_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_446_ = lean_string_append(v___x_444_, v___x_445_);
v___y_410_ = v___y_428_;
v___y_411_ = v___y_431_;
v___y_412_ = v___y_430_;
v___y_413_ = v___y_429_;
v___y_414_ = v___y_432_;
v___y_415_ = v___y_437_;
v___y_416_ = v___y_433_;
v___y_417_ = v___y_434_;
v_port_418_ = v_port_436_;
v___y_419_ = v___x_446_;
goto v___jp_409_;
}
}
}
v___jp_447_:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_string_append(v___y_448_, v___y_451_);
lean_dec_ref(v___y_451_);
v___x_454_ = lean_string_append(v___x_453_, v___y_452_);
lean_dec_ref(v___y_452_);
v___y_332_ = v___y_449_;
v___y_333_ = v___y_450_;
v___y_334_ = v___x_454_;
goto v___jp_331_;
}
v___jp_455_:
{
switch(lean_obj_tag(v_port_459_))
{
case 0:
{
lean_object* v___x_461_; 
v___x_461_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_448_ = v___y_456_;
v___y_449_ = v___y_457_;
v___y_450_ = v___y_458_;
v___y_451_ = v___y_460_;
v___y_452_ = v___x_461_;
goto v___jp_447_;
}
case 1:
{
lean_object* v___x_462_; 
v___x_462_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_448_ = v___y_456_;
v___y_449_ = v___y_457_;
v___y_450_ = v___y_458_;
v___y_451_ = v___y_460_;
v___y_452_ = v___x_462_;
goto v___jp_447_;
}
default: 
{
uint16_t v_port_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_port_463_ = lean_ctor_get_uint16(v_port_459_, 0);
lean_dec_ref_known(v_port_459_, 0);
v___x_464_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_465_ = lean_uint16_to_nat(v_port_463_);
v___x_466_ = l_Nat_reprFast(v___x_465_);
v___x_467_ = lean_string_append(v___x_464_, v___x_466_);
lean_dec_ref(v___x_466_);
v___y_448_ = v___y_456_;
v___y_449_ = v___y_457_;
v___y_450_ = v___y_458_;
v___y_451_ = v___y_460_;
v___y_452_ = v___x_467_;
goto v___jp_447_;
}
}
}
v___jp_468_:
{
switch(lean_obj_tag(v_host_471_))
{
case 0:
{
lean_object* v_name_474_; 
v_name_474_ = lean_ctor_get(v_host_471_, 0);
lean_inc_ref(v_name_474_);
lean_dec_ref_known(v_host_471_, 1);
v___y_456_ = v___y_473_;
v___y_457_ = v___y_469_;
v___y_458_ = v___y_470_;
v_port_459_ = v_port_472_;
v___y_460_ = v_name_474_;
goto v___jp_455_;
}
case 1:
{
lean_object* v_ipv4_475_; lean_object* v___x_476_; 
v_ipv4_475_ = lean_ctor_get(v_host_471_, 0);
lean_inc_ref(v_ipv4_475_);
lean_dec_ref_known(v_host_471_, 1);
v___x_476_ = lean_uv_ntop_v4(v_ipv4_475_);
lean_dec_ref(v_ipv4_475_);
v___y_456_ = v___y_473_;
v___y_457_ = v___y_469_;
v___y_458_ = v___y_470_;
v_port_459_ = v_port_472_;
v___y_460_ = v___x_476_;
goto v___jp_455_;
}
default: 
{
lean_object* v_ipv6_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v_ipv6_477_ = lean_ctor_get(v_host_471_, 0);
lean_inc_ref(v_ipv6_477_);
lean_dec_ref_known(v_host_471_, 1);
v___x_478_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_479_ = lean_uv_ntop_v6(v_ipv6_477_);
lean_dec_ref(v_ipv6_477_);
v___x_480_ = lean_string_append(v___x_478_, v___x_479_);
lean_dec_ref(v___x_479_);
v___x_481_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_482_ = lean_string_append(v___x_480_, v___x_481_);
v___y_456_ = v___y_473_;
v___y_457_ = v___y_469_;
v___y_458_ = v___y_470_;
v_port_459_ = v_port_472_;
v___y_460_ = v___x_482_;
goto v___jp_455_;
}
}
}
v___jp_483_:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__20));
lean_inc_ref(v___y_484_);
v___x_486_ = lean_string_append(v___y_484_, v___x_485_);
switch(lean_obj_tag(v_uri_314_))
{
case 0:
{
lean_object* v_path_487_; lean_object* v_query_488_; lean_object* v_segments_489_; uint8_t v_absolute_490_; lean_object* v___x_491_; lean_object* v___x_492_; size_t v_sz_493_; size_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_result_497_; 
lean_dec_ref(v___f_309_);
v_path_487_ = lean_ctor_get(v_uri_314_, 0);
lean_inc_ref(v_path_487_);
v_query_488_ = lean_ctor_get(v_uri_314_, 1);
lean_inc(v_query_488_);
lean_dec_ref_known(v_uri_314_, 2);
v_segments_489_ = lean_ctor_get(v_path_487_, 0);
lean_inc_ref(v_segments_489_);
v_absolute_490_ = lean_ctor_get_uint8(v_path_487_, sizeof(void*)*1);
lean_dec_ref(v_path_487_);
v___x_491_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_492_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_493_ = lean_array_size(v_segments_489_);
v___x_494_ = ((size_t)0ULL);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_492_, v___f_310_, v_sz_493_, v___x_494_, v_segments_489_);
v___x_496_ = lean_array_to_list(v___x_495_);
v_result_497_ = l_String_intercalate(v___x_491_, v___x_496_);
if (v_absolute_490_ == 0)
{
v___y_342_ = v___x_486_;
v___y_343_ = v___x_485_;
v___y_344_ = v_query_488_;
v___y_345_ = v_result_497_;
goto v___jp_341_;
}
else
{
lean_object* v___x_498_; 
v___x_498_ = lean_string_append(v___x_491_, v_result_497_);
lean_dec_ref(v_result_497_);
v___y_342_ = v___x_486_;
v___y_343_ = v___x_485_;
v___y_344_ = v_query_488_;
v___y_345_ = v___x_498_;
goto v___jp_341_;
}
}
case 1:
{
lean_object* v_uri_499_; lean_object* v_authority_500_; 
lean_dec_ref(v___f_310_);
v_uri_499_ = lean_ctor_get(v_uri_314_, 0);
lean_inc_ref(v_uri_499_);
lean_dec_ref_known(v_uri_314_, 1);
v_authority_500_ = lean_ctor_get(v_uri_499_, 1);
if (lean_obj_tag(v_authority_500_) == 0)
{
lean_object* v_scheme_501_; lean_object* v_path_502_; lean_object* v_query_503_; lean_object* v_fragment_504_; lean_object* v___x_505_; 
v_scheme_501_ = lean_ctor_get(v_uri_499_, 0);
lean_inc_ref(v_scheme_501_);
v_path_502_ = lean_ctor_get(v_uri_499_, 2);
lean_inc_ref(v_path_502_);
v_query_503_ = lean_ctor_get(v_uri_499_, 3);
lean_inc(v_query_503_);
v_fragment_504_ = lean_ctor_get(v_uri_499_, 4);
lean_inc(v_fragment_504_);
lean_dec_ref(v_uri_499_);
v___x_505_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_378_ = v_path_502_;
v___y_379_ = v_query_503_;
v___y_380_ = v_scheme_501_;
v___y_381_ = v_fragment_504_;
v___y_382_ = v___x_486_;
v___y_383_ = v___x_485_;
v___y_384_ = v___x_505_;
goto v___jp_377_;
}
else
{
lean_object* v_val_506_; lean_object* v_scheme_507_; lean_object* v_path_508_; lean_object* v_query_509_; lean_object* v_fragment_510_; lean_object* v_userInfo_511_; lean_object* v_host_512_; lean_object* v_port_513_; lean_object* v___x_514_; 
v_val_506_ = lean_ctor_get(v_authority_500_, 0);
lean_inc(v_val_506_);
v_scheme_507_ = lean_ctor_get(v_uri_499_, 0);
lean_inc_ref(v_scheme_507_);
v_path_508_ = lean_ctor_get(v_uri_499_, 2);
lean_inc_ref(v_path_508_);
v_query_509_ = lean_ctor_get(v_uri_499_, 3);
lean_inc(v_query_509_);
v_fragment_510_ = lean_ctor_get(v_uri_499_, 4);
lean_inc(v_fragment_510_);
lean_dec_ref(v_uri_499_);
v_userInfo_511_ = lean_ctor_get(v_val_506_, 0);
lean_inc(v_userInfo_511_);
v_host_512_ = lean_ctor_get(v_val_506_, 1);
lean_inc_ref(v_host_512_);
v_port_513_ = lean_ctor_get(v_val_506_, 2);
lean_inc(v_port_513_);
lean_dec(v_val_506_);
v___x_514_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__21));
if (lean_obj_tag(v_userInfo_511_) == 0)
{
lean_object* v___x_515_; 
v___x_515_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_428_ = v_path_508_;
v___y_429_ = v_fragment_510_;
v___y_430_ = v_scheme_507_;
v___y_431_ = v_query_509_;
v___y_432_ = v___x_514_;
v___y_433_ = v___x_486_;
v___y_434_ = v___x_485_;
v_host_435_ = v_host_512_;
v_port_436_ = v_port_513_;
v___y_437_ = v___x_515_;
goto v___jp_427_;
}
else
{
lean_object* v_val_516_; lean_object* v_password_517_; 
v_val_516_ = lean_ctor_get(v_userInfo_511_, 0);
lean_inc(v_val_516_);
lean_dec_ref_known(v_userInfo_511_, 1);
v_password_517_ = lean_ctor_get(v_val_516_, 1);
if (lean_obj_tag(v_password_517_) == 0)
{
lean_object* v_username_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_username_518_ = lean_ctor_get(v_val_516_, 0);
lean_inc_ref(v_username_518_);
lean_dec(v_val_516_);
v___x_519_ = lean_string_from_utf8_unchecked(v_username_518_);
v___x_520_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_521_ = lean_string_append(v___x_519_, v___x_520_);
v___y_428_ = v_path_508_;
v___y_429_ = v_fragment_510_;
v___y_430_ = v_scheme_507_;
v___y_431_ = v_query_509_;
v___y_432_ = v___x_514_;
v___y_433_ = v___x_486_;
v___y_434_ = v___x_485_;
v_host_435_ = v_host_512_;
v_port_436_ = v_port_513_;
v___y_437_ = v___x_521_;
goto v___jp_427_;
}
else
{
lean_object* v_username_522_; lean_object* v_val_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
lean_inc_ref(v_password_517_);
v_username_522_ = lean_ctor_get(v_val_516_, 0);
lean_inc_ref(v_username_522_);
lean_dec(v_val_516_);
v_val_523_ = lean_ctor_get(v_password_517_, 0);
lean_inc(v_val_523_);
lean_dec_ref_known(v_password_517_, 1);
v___x_524_ = lean_string_from_utf8_unchecked(v_username_522_);
v___x_525_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_526_ = lean_string_append(v___x_524_, v___x_525_);
v___x_527_ = lean_string_from_utf8_unchecked(v_val_523_);
v___x_528_ = lean_string_append(v___x_526_, v___x_527_);
lean_dec_ref(v___x_527_);
v___x_529_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_530_ = lean_string_append(v___x_528_, v___x_529_);
v___y_428_ = v_path_508_;
v___y_429_ = v_fragment_510_;
v___y_430_ = v_scheme_507_;
v___y_431_ = v_query_509_;
v___y_432_ = v___x_514_;
v___y_433_ = v___x_486_;
v___y_434_ = v___x_485_;
v_host_435_ = v_host_512_;
v_port_436_ = v_port_513_;
v___y_437_ = v___x_530_;
goto v___jp_427_;
}
}
}
}
case 2:
{
lean_object* v_authority_531_; lean_object* v_userInfo_532_; 
lean_dec_ref(v___f_310_);
lean_dec_ref(v___f_309_);
v_authority_531_ = lean_ctor_get(v_uri_314_, 0);
lean_inc_ref(v_authority_531_);
lean_dec_ref_known(v_uri_314_, 1);
v_userInfo_532_ = lean_ctor_get(v_authority_531_, 0);
if (lean_obj_tag(v_userInfo_532_) == 0)
{
lean_object* v_host_533_; lean_object* v_port_534_; lean_object* v___x_535_; 
v_host_533_ = lean_ctor_get(v_authority_531_, 1);
lean_inc_ref(v_host_533_);
v_port_534_ = lean_ctor_get(v_authority_531_, 2);
lean_inc(v_port_534_);
lean_dec_ref(v_authority_531_);
v___x_535_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_469_ = v___x_486_;
v___y_470_ = v___x_485_;
v_host_471_ = v_host_533_;
v_port_472_ = v_port_534_;
v___y_473_ = v___x_535_;
goto v___jp_468_;
}
else
{
lean_object* v_val_536_; lean_object* v_password_537_; 
v_val_536_ = lean_ctor_get(v_userInfo_532_, 0);
lean_inc(v_val_536_);
v_password_537_ = lean_ctor_get(v_val_536_, 1);
if (lean_obj_tag(v_password_537_) == 0)
{
lean_object* v_host_538_; lean_object* v_port_539_; lean_object* v_username_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v_host_538_ = lean_ctor_get(v_authority_531_, 1);
lean_inc_ref(v_host_538_);
v_port_539_ = lean_ctor_get(v_authority_531_, 2);
lean_inc(v_port_539_);
lean_dec_ref(v_authority_531_);
v_username_540_ = lean_ctor_get(v_val_536_, 0);
lean_inc_ref(v_username_540_);
lean_dec(v_val_536_);
v___x_541_ = lean_string_from_utf8_unchecked(v_username_540_);
v___x_542_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_543_ = lean_string_append(v___x_541_, v___x_542_);
v___y_469_ = v___x_486_;
v___y_470_ = v___x_485_;
v_host_471_ = v_host_538_;
v_port_472_ = v_port_539_;
v___y_473_ = v___x_543_;
goto v___jp_468_;
}
else
{
lean_object* v_host_544_; lean_object* v_port_545_; lean_object* v_username_546_; lean_object* v_val_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
lean_inc_ref(v_password_537_);
v_host_544_ = lean_ctor_get(v_authority_531_, 1);
lean_inc_ref(v_host_544_);
v_port_545_ = lean_ctor_get(v_authority_531_, 2);
lean_inc(v_port_545_);
lean_dec_ref(v_authority_531_);
v_username_546_ = lean_ctor_get(v_val_536_, 0);
lean_inc_ref(v_username_546_);
lean_dec(v_val_536_);
v_val_547_ = lean_ctor_get(v_password_537_, 0);
lean_inc(v_val_547_);
lean_dec_ref_known(v_password_537_, 1);
v___x_548_ = lean_string_from_utf8_unchecked(v_username_546_);
v___x_549_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_550_ = lean_string_append(v___x_548_, v___x_549_);
v___x_551_ = lean_string_from_utf8_unchecked(v_val_547_);
v___x_552_ = lean_string_append(v___x_550_, v___x_551_);
lean_dec_ref(v___x_551_);
v___x_553_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_554_ = lean_string_append(v___x_552_, v___x_553_);
v___y_469_ = v___x_486_;
v___y_470_ = v___x_485_;
v_host_471_ = v_host_544_;
v_port_472_ = v_port_545_;
v___y_473_ = v___x_554_;
goto v___jp_468_;
}
}
}
default: 
{
lean_object* v___x_555_; 
lean_dec_ref(v___f_310_);
lean_dec_ref(v___f_309_);
v___x_555_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__23));
v___y_332_ = v___x_486_;
v___y_333_ = v___x_485_;
v___y_334_ = v___x_555_;
goto v___jp_331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1(lean_object* v___x_602_, lean_object* v___x_603_, lean_object* v___x_604_, lean_object* v_name_605_, lean_object* v___x_606_, uint32_t v___x_607_, lean_object* v___x_608_, lean_object* v_it_609_, lean_object* v_acc_610_, lean_object* v_hP_611_, lean_object* v_recur_612_){
_start:
{
lean_object* v_it_614_; lean_object* v_out_615_; lean_object* v___y_631_; lean_object* v___y_632_; uint32_t v___y_633_; uint8_t v___y_634_; lean_object* v_it_640_; lean_object* v_startInclusive_641_; lean_object* v_endExclusive_642_; 
if (lean_obj_tag(v_it_609_) == 0)
{
lean_object* v_currPos_649_; lean_object* v_searcher_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_672_; 
v_currPos_649_ = lean_ctor_get(v_it_609_, 0);
v_searcher_650_ = lean_ctor_get(v_it_609_, 1);
v_isSharedCheck_672_ = !lean_is_exclusive(v_it_609_);
if (v_isSharedCheck_672_ == 0)
{
v___x_652_ = v_it_609_;
v_isShared_653_ = v_isSharedCheck_672_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_searcher_650_);
lean_inc(v_currPos_649_);
lean_dec(v_it_609_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_672_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
uint8_t v_decide_654_; 
v_decide_654_ = lean_nat_dec_eq(v_searcher_650_, v___x_606_);
if (v_decide_654_ == 0)
{
uint32_t v___x_655_; uint8_t v___x_656_; 
lean_dec(v___x_606_);
v___x_655_ = lean_string_utf8_get_fast(v_name_605_, v_searcher_650_);
v___x_656_ = lean_uint32_dec_eq(v___x_655_, v___x_607_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_657_ = lean_string_utf8_next_fast(v_name_605_, v_searcher_650_);
lean_dec(v_searcher_650_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v___x_657_);
v___x_659_ = v___x_652_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_currPos_649_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v___x_657_);
v___x_659_ = v_reuseFailAlloc_661_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_660_; 
v___x_660_ = lean_apply_4(v_recur_612_, v___x_659_, v_acc_610_, lean_box(0), lean_box(0));
return v___x_660_;
}
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v_slice_665_; lean_object* v_nextIt_667_; 
v___x_662_ = lean_string_utf8_next_fast(v_name_605_, v_searcher_650_);
v___x_663_ = lean_nat_sub(v___x_662_, v_searcher_650_);
v___x_664_ = lean_nat_add(v_searcher_650_, v___x_663_);
lean_dec(v___x_663_);
v_slice_665_ = l_String_Slice_subslice_x21(v___x_608_, v_currPos_649_, v_searcher_650_);
lean_inc(v___x_664_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v___x_664_);
lean_ctor_set(v___x_652_, 0, v___x_664_);
v_nextIt_667_ = v___x_652_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v___x_664_);
v_nextIt_667_ = v_reuseFailAlloc_670_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v_startInclusive_668_; lean_object* v_endExclusive_669_; 
v_startInclusive_668_ = lean_ctor_get(v_slice_665_, 0);
lean_inc(v_startInclusive_668_);
v_endExclusive_669_ = lean_ctor_get(v_slice_665_, 1);
lean_inc(v_endExclusive_669_);
lean_dec_ref(v_slice_665_);
v_it_640_ = v_nextIt_667_;
v_startInclusive_641_ = v_startInclusive_668_;
v_endExclusive_642_ = v_endExclusive_669_;
goto v___jp_639_;
}
}
}
else
{
lean_object* v___x_671_; 
lean_del_object(v___x_652_);
lean_dec(v_searcher_650_);
v___x_671_ = lean_box(1);
v_it_640_ = v___x_671_;
v_startInclusive_641_ = v_currPos_649_;
v_endExclusive_642_ = v___x_606_;
goto v___jp_639_;
}
}
}
else
{
lean_dec_ref(v_recur_612_);
lean_dec(v___x_606_);
return v_acc_610_;
}
v___jp_613_:
{
if (lean_obj_tag(v_acc_610_) == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v_out_615_);
v___x_617_ = lean_apply_4(v_recur_612_, v_it_614_, v___x_616_, lean_box(0), lean_box(0));
return v___x_617_;
}
else
{
lean_object* v_val_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_629_; 
v_val_618_ = lean_ctor_get(v_acc_610_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v_acc_610_);
if (v_isSharedCheck_629_ == 0)
{
v___x_620_ = v_acc_610_;
v_isShared_621_ = v_isSharedCheck_629_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_val_618_);
lean_dec(v_acc_610_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_629_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_622_ = lean_string_utf8_extract_fast(v___x_602_, v___x_603_, v___x_604_);
v___x_623_ = lean_string_append(v_val_618_, v___x_622_);
lean_dec_ref(v___x_622_);
v___x_624_ = lean_string_append(v___x_623_, v_out_615_);
lean_dec_ref(v_out_615_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_624_);
v___x_626_ = v___x_620_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_628_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; 
v___x_627_ = lean_apply_4(v_recur_612_, v_it_614_, v___x_626_, lean_box(0), lean_box(0));
return v___x_627_;
}
}
}
}
v___jp_630_:
{
if (v___y_634_ == 0)
{
lean_object* v___x_635_; 
v___x_635_ = lean_string_utf8_set(v___y_631_, v___x_603_, v___y_633_);
v_it_614_ = v___y_632_;
v_out_615_ = v___x_635_;
goto v___jp_613_;
}
else
{
uint32_t v___x_636_; uint32_t v___x_637_; lean_object* v___x_638_; 
v___x_636_ = 4294967264;
v___x_637_ = lean_uint32_add(v___y_633_, v___x_636_);
v___x_638_ = lean_string_utf8_set(v___y_631_, v___x_603_, v___x_637_);
v_it_614_ = v___y_632_;
v_out_615_ = v___x_638_;
goto v___jp_613_;
}
}
v___jp_639_:
{
lean_object* v___x_643_; uint32_t v___x_644_; uint32_t v___x_645_; uint8_t v___x_646_; 
v___x_643_ = lean_string_utf8_extract_fast(v_name_605_, v_startInclusive_641_, v_endExclusive_642_);
lean_dec(v_endExclusive_642_);
lean_dec(v_startInclusive_641_);
v___x_644_ = lean_string_utf8_get(v___x_643_, v___x_603_);
v___x_645_ = 97;
v___x_646_ = lean_uint32_dec_le(v___x_645_, v___x_644_);
if (v___x_646_ == 0)
{
v___y_631_ = v___x_643_;
v___y_632_ = v_it_640_;
v___y_633_ = v___x_644_;
v___y_634_ = v___x_646_;
goto v___jp_630_;
}
else
{
uint32_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = 122;
v___x_648_ = lean_uint32_dec_le(v___x_644_, v___x_647_);
v___y_631_ = v___x_643_;
v___y_632_ = v_it_640_;
v___y_633_ = v___x_644_;
v___y_634_ = v___x_648_;
goto v___jp_630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1___boxed(lean_object* v___x_673_, lean_object* v___x_674_, lean_object* v___x_675_, lean_object* v_name_676_, lean_object* v___x_677_, lean_object* v___x_678_, lean_object* v___x_679_, lean_object* v_it_680_, lean_object* v_acc_681_, lean_object* v_hP_682_, lean_object* v_recur_683_){
_start:
{
uint32_t v___x_3102__boxed_684_; lean_object* v_res_685_; 
v___x_3102__boxed_684_ = lean_unbox_uint32(v___x_678_);
lean_dec(v___x_678_);
v_res_685_ = l_Std_Http_Request_instEncodeV11Head___lam__1(v___x_673_, v___x_674_, v___x_675_, v_name_676_, v___x_677_, v___x_3102__boxed_684_, v___x_679_, v_it_680_, v_acc_681_, v_hP_682_, v_recur_683_);
lean_dec_ref(v___x_679_);
lean_dec_ref(v_name_676_);
lean_dec(v___x_675_);
lean_dec(v___x_674_);
lean_dec_ref(v___x_673_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0(lean_object* v_buf_686_, lean_object* v_name_687_, lean_object* v_value_688_){
_start:
{
lean_object* v___y_690_; lean_object* v___f_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_it_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___f_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___f_709_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__1));
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = lean_string_utf8_byte_size(v_name_687_);
lean_inc_ref(v_name_687_);
v___x_712_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_712_, 0, v_name_687_);
lean_ctor_set(v___x_712_, 1, v___x_710_);
lean_ctor_set(v___x_712_, 2, v___x_711_);
lean_inc_ref(v___x_712_);
v_it_713_ = l_String_Slice_splitToSubslice___redArg(v___x_712_, v___f_709_);
v___x_714_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__2));
v___x_715_ = lean_unsigned_to_nat(1u);
v___x_716_ = l_Std_Http_Request_instToStringHead___lam__2___boxed__const__1;
v___f_717_ = lean_alloc_closure((void*)(l_Std_Http_Request_instEncodeV11Head___lam__1___boxed), 11, 7);
lean_closure_set(v___f_717_, 0, v___x_714_);
lean_closure_set(v___f_717_, 1, v___x_710_);
lean_closure_set(v___f_717_, 2, v___x_715_);
lean_closure_set(v___f_717_, 3, v_name_687_);
lean_closure_set(v___f_717_, 4, v___x_711_);
lean_closure_set(v___f_717_, 5, v___x_716_);
lean_closure_set(v___f_717_, 6, v___x_712_);
v___x_718_ = lean_box(0);
v___x_719_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_717_, v_it_713_, v___x_718_, lean_box(0));
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___x_720_; 
v___x_720_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_690_ = v___x_720_;
goto v___jp_689_;
}
else
{
lean_object* v_val_721_; 
v_val_721_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_val_721_);
lean_dec_ref_known(v___x_719_, 1);
v___y_690_ = v_val_721_;
goto v___jp_689_;
}
v___jp_689_:
{
lean_object* v_data_691_; lean_object* v_size_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_708_; 
v_data_691_ = lean_ctor_get(v_buf_686_, 0);
v_size_692_ = lean_ctor_get(v_buf_686_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_buf_686_);
if (v_isSharedCheck_708_ == 0)
{
v___x_694_ = v_buf_686_;
v_isShared_695_ = v_isSharedCheck_708_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_size_692_);
lean_inc(v_data_691_);
lean_dec(v_buf_686_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_708_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_696_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__0));
v___x_697_ = lean_string_append(v___y_690_, v___x_696_);
v___x_698_ = lean_string_append(v___x_697_, v_value_688_);
v___x_699_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__0));
v___x_700_ = lean_string_append(v___x_698_, v___x_699_);
v___x_701_ = lean_string_to_utf8(v___x_700_);
lean_dec_ref(v___x_700_);
lean_inc_ref(v___x_701_);
v___x_702_ = lean_array_push(v_data_691_, v___x_701_);
v___x_703_ = lean_byte_array_size(v___x_701_);
lean_dec_ref(v___x_701_);
v___x_704_ = lean_nat_add(v_size_692_, v___x_703_);
lean_dec(v_size_692_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v___x_704_);
lean_ctor_set(v___x_694_, 0, v___x_702_);
v___x_706_ = v___x_694_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___boxed(lean_object* v_buf_722_, lean_object* v_name_723_, lean_object* v_value_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Std_Http_Request_instEncodeV11Head___lam__0(v_buf_722_, v_name_723_, v_value_724_);
lean_dec_ref(v_value_724_);
return v_res_725_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__0));
v___x_727_ = lean_string_to_utf8(v___x_726_);
return v___x_727_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0);
v___x_729_ = lean_byte_array_size(v___x_728_);
return v___x_729_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = ((lean_object*)(l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2));
v___x_737_ = lean_byte_array_size(v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3(lean_object* v___f_738_, lean_object* v___f_739_, lean_object* v___f_740_, lean_object* v_buffer_741_, lean_object* v_req_742_){
_start:
{
uint8_t v_method_743_; uint8_t v_version_744_; lean_object* v_uri_745_; lean_object* v_headers_746_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_799_; lean_object* v_port_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v_host_816_; lean_object* v_port_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v_port_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v_host_925_; lean_object* v_port_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_951_; 
v_method_743_ = lean_ctor_get_uint8(v_req_742_, sizeof(void*)*2);
v_version_744_ = lean_ctor_get_uint8(v_req_742_, sizeof(void*)*2 + 1);
v_uri_745_ = lean_ctor_get(v_req_742_, 0);
lean_inc(v_uri_745_);
v_headers_746_ = lean_ctor_get(v_req_742_, 1);
lean_inc_ref(v_headers_746_);
lean_dec_ref(v_req_742_);
switch(v_method_743_)
{
case 0:
{
lean_object* v___x_1031_; 
v___x_1031_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__24));
v___y_951_ = v___x_1031_;
goto v___jp_950_;
}
case 1:
{
lean_object* v___x_1032_; 
v___x_1032_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__25));
v___y_951_ = v___x_1032_;
goto v___jp_950_;
}
case 2:
{
lean_object* v___x_1033_; 
v___x_1033_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__26));
v___y_951_ = v___x_1033_;
goto v___jp_950_;
}
case 3:
{
lean_object* v___x_1034_; 
v___x_1034_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__27));
v___y_951_ = v___x_1034_;
goto v___jp_950_;
}
case 4:
{
lean_object* v___x_1035_; 
v___x_1035_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__28));
v___y_951_ = v___x_1035_;
goto v___jp_950_;
}
case 5:
{
lean_object* v___x_1036_; 
v___x_1036_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__29));
v___y_951_ = v___x_1036_;
goto v___jp_950_;
}
case 6:
{
lean_object* v___x_1037_; 
v___x_1037_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__30));
v___y_951_ = v___x_1037_;
goto v___jp_950_;
}
case 7:
{
lean_object* v___x_1038_; 
v___x_1038_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__31));
v___y_951_ = v___x_1038_;
goto v___jp_950_;
}
case 8:
{
lean_object* v___x_1039_; 
v___x_1039_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__32));
v___y_951_ = v___x_1039_;
goto v___jp_950_;
}
case 9:
{
lean_object* v___x_1040_; 
v___x_1040_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__33));
v___y_951_ = v___x_1040_;
goto v___jp_950_;
}
case 10:
{
lean_object* v___x_1041_; 
v___x_1041_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__34));
v___y_951_ = v___x_1041_;
goto v___jp_950_;
}
case 11:
{
lean_object* v___x_1042_; 
v___x_1042_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__35));
v___y_951_ = v___x_1042_;
goto v___jp_950_;
}
case 12:
{
lean_object* v___x_1043_; 
v___x_1043_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__36));
v___y_951_ = v___x_1043_;
goto v___jp_950_;
}
case 13:
{
lean_object* v___x_1044_; 
v___x_1044_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__37));
v___y_951_ = v___x_1044_;
goto v___jp_950_;
}
case 14:
{
lean_object* v___x_1045_; 
v___x_1045_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__38));
v___y_951_ = v___x_1045_;
goto v___jp_950_;
}
case 15:
{
lean_object* v___x_1046_; 
v___x_1046_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__39));
v___y_951_ = v___x_1046_;
goto v___jp_950_;
}
case 16:
{
lean_object* v___x_1047_; 
v___x_1047_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__40));
v___y_951_ = v___x_1047_;
goto v___jp_950_;
}
case 17:
{
lean_object* v___x_1048_; 
v___x_1048_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__41));
v___y_951_ = v___x_1048_;
goto v___jp_950_;
}
case 18:
{
lean_object* v___x_1049_; 
v___x_1049_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__42));
v___y_951_ = v___x_1049_;
goto v___jp_950_;
}
case 19:
{
lean_object* v___x_1050_; 
v___x_1050_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__43));
v___y_951_ = v___x_1050_;
goto v___jp_950_;
}
case 20:
{
lean_object* v___x_1051_; 
v___x_1051_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__44));
v___y_951_ = v___x_1051_;
goto v___jp_950_;
}
case 21:
{
lean_object* v___x_1052_; 
v___x_1052_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__45));
v___y_951_ = v___x_1052_;
goto v___jp_950_;
}
case 22:
{
lean_object* v___x_1053_; 
v___x_1053_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__46));
v___y_951_ = v___x_1053_;
goto v___jp_950_;
}
case 23:
{
lean_object* v___x_1054_; 
v___x_1054_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__47));
v___y_951_ = v___x_1054_;
goto v___jp_950_;
}
case 24:
{
lean_object* v___x_1055_; 
v___x_1055_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__48));
v___y_951_ = v___x_1055_;
goto v___jp_950_;
}
case 25:
{
lean_object* v___x_1056_; 
v___x_1056_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__49));
v___y_951_ = v___x_1056_;
goto v___jp_950_;
}
case 26:
{
lean_object* v___x_1057_; 
v___x_1057_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__50));
v___y_951_ = v___x_1057_;
goto v___jp_950_;
}
case 27:
{
lean_object* v___x_1058_; 
v___x_1058_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__51));
v___y_951_ = v___x_1058_;
goto v___jp_950_;
}
case 28:
{
lean_object* v___x_1059_; 
v___x_1059_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__52));
v___y_951_ = v___x_1059_;
goto v___jp_950_;
}
case 29:
{
lean_object* v___x_1060_; 
v___x_1060_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__53));
v___y_951_ = v___x_1060_;
goto v___jp_950_;
}
case 30:
{
lean_object* v___x_1061_; 
v___x_1061_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__54));
v___y_951_ = v___x_1061_;
goto v___jp_950_;
}
case 31:
{
lean_object* v___x_1062_; 
v___x_1062_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__55));
v___y_951_ = v___x_1062_;
goto v___jp_950_;
}
case 32:
{
lean_object* v___x_1063_; 
v___x_1063_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__56));
v___y_951_ = v___x_1063_;
goto v___jp_950_;
}
case 33:
{
lean_object* v___x_1064_; 
v___x_1064_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__57));
v___y_951_ = v___x_1064_;
goto v___jp_950_;
}
case 34:
{
lean_object* v___x_1065_; 
v___x_1065_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__58));
v___y_951_ = v___x_1065_;
goto v___jp_950_;
}
case 35:
{
lean_object* v___x_1066_; 
v___x_1066_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__59));
v___y_951_ = v___x_1066_;
goto v___jp_950_;
}
case 36:
{
lean_object* v___x_1067_; 
v___x_1067_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__60));
v___y_951_ = v___x_1067_;
goto v___jp_950_;
}
case 37:
{
lean_object* v___x_1068_; 
v___x_1068_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__61));
v___y_951_ = v___x_1068_;
goto v___jp_950_;
}
case 38:
{
lean_object* v___x_1069_; 
v___x_1069_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__62));
v___y_951_ = v___x_1069_;
goto v___jp_950_;
}
default: 
{
lean_object* v___x_1070_; 
v___x_1070_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__63));
v___y_951_ = v___x_1070_;
goto v___jp_950_;
}
}
v___jp_747_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_buffer_759_; lean_object* v_buffer_760_; lean_object* v_data_761_; lean_object* v_size_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_771_; 
v___x_751_ = lean_string_to_utf8(v___y_750_);
lean_inc_ref(v___x_751_);
v___x_752_ = lean_array_push(v___y_749_, v___x_751_);
v___x_753_ = lean_byte_array_size(v___x_751_);
lean_dec_ref(v___x_751_);
v___x_754_ = lean_nat_add(v___y_748_, v___x_753_);
lean_dec(v___y_748_);
v___x_755_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__0);
v___x_756_ = lean_array_push(v___x_752_, v___x_755_);
v___x_757_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__1);
v___x_758_ = lean_nat_add(v___x_754_, v___x_757_);
lean_dec(v___x_754_);
v_buffer_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_759_, 0, v___x_756_);
lean_ctor_set(v_buffer_759_, 1, v___x_758_);
v_buffer_760_ = l_Std_Http_Headers_fold___redArg(v_headers_746_, v_buffer_759_, v___f_738_);
lean_dec_ref(v_headers_746_);
v_data_761_ = lean_ctor_get(v_buffer_760_, 0);
v_size_762_ = lean_ctor_get(v_buffer_760_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v_buffer_760_);
if (v_isSharedCheck_771_ == 0)
{
v___x_764_ = v_buffer_760_;
v_isShared_765_ = v_isSharedCheck_771_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_size_762_);
lean_inc(v_data_761_);
lean_dec(v_buffer_760_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_771_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_766_ = lean_array_push(v_data_761_, v___x_755_);
v___x_767_ = lean_nat_add(v_size_762_, v___x_757_);
lean_dec(v_size_762_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 1, v___x_767_);
lean_ctor_set(v___x_764_, 0, v___x_766_);
v___x_769_ = v___x_764_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
v___jp_772_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_778_ = lean_string_to_utf8(v___y_777_);
lean_dec_ref(v___y_777_);
lean_inc_ref(v___x_778_);
v___x_779_ = lean_array_push(v___y_776_, v___x_778_);
v___x_780_ = lean_byte_array_size(v___x_778_);
lean_dec_ref(v___x_778_);
v___x_781_ = lean_nat_add(v___y_775_, v___x_780_);
lean_dec(v___y_775_);
v___x_782_ = lean_array_push(v___x_779_, v___y_773_);
v___x_783_ = lean_nat_add(v___x_781_, v___y_774_);
lean_dec(v___x_781_);
switch(v_version_744_)
{
case 0:
{
lean_object* v___x_784_; 
v___x_784_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__11));
v___y_748_ = v___x_783_;
v___y_749_ = v___x_782_;
v___y_750_ = v___x_784_;
goto v___jp_747_;
}
case 1:
{
lean_object* v___x_785_; 
v___x_785_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__12));
v___y_748_ = v___x_783_;
v___y_749_ = v___x_782_;
v___y_750_ = v___x_785_;
goto v___jp_747_;
}
case 2:
{
lean_object* v___x_786_; 
v___x_786_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__13));
v___y_748_ = v___x_783_;
v___y_749_ = v___x_782_;
v___y_750_ = v___x_786_;
goto v___jp_747_;
}
default: 
{
lean_object* v___x_787_; 
v___x_787_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__14));
v___y_748_ = v___x_783_;
v___y_749_ = v___x_782_;
v___y_750_ = v___x_787_;
goto v___jp_747_;
}
}
}
v___jp_788_:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_string_append(v___y_793_, v___y_789_);
lean_dec_ref(v___y_789_);
v___x_797_ = lean_string_append(v___x_796_, v___y_795_);
lean_dec_ref(v___y_795_);
v___y_773_ = v___y_790_;
v___y_774_ = v___y_791_;
v___y_775_ = v___y_792_;
v___y_776_ = v___y_794_;
v___y_777_ = v___x_797_;
goto v___jp_772_;
}
v___jp_798_:
{
switch(lean_obj_tag(v_port_800_))
{
case 0:
{
lean_object* v___x_806_; 
v___x_806_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_789_ = v___y_805_;
v___y_790_ = v___y_799_;
v___y_791_ = v___y_801_;
v___y_792_ = v___y_802_;
v___y_793_ = v___y_803_;
v___y_794_ = v___y_804_;
v___y_795_ = v___x_806_;
goto v___jp_788_;
}
case 1:
{
lean_object* v___x_807_; 
v___x_807_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_789_ = v___y_805_;
v___y_790_ = v___y_799_;
v___y_791_ = v___y_801_;
v___y_792_ = v___y_802_;
v___y_793_ = v___y_803_;
v___y_794_ = v___y_804_;
v___y_795_ = v___x_807_;
goto v___jp_788_;
}
default: 
{
uint16_t v_port_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v_port_808_ = lean_ctor_get_uint16(v_port_800_, 0);
lean_dec_ref_known(v_port_800_, 0);
v___x_809_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_810_ = lean_uint16_to_nat(v_port_808_);
v___x_811_ = l_Nat_reprFast(v___x_810_);
v___x_812_ = lean_string_append(v___x_809_, v___x_811_);
lean_dec_ref(v___x_811_);
v___y_789_ = v___y_805_;
v___y_790_ = v___y_799_;
v___y_791_ = v___y_801_;
v___y_792_ = v___y_802_;
v___y_793_ = v___y_803_;
v___y_794_ = v___y_804_;
v___y_795_ = v___x_812_;
goto v___jp_788_;
}
}
}
v___jp_813_:
{
switch(lean_obj_tag(v_host_816_))
{
case 0:
{
lean_object* v_name_821_; 
v_name_821_ = lean_ctor_get(v_host_816_, 0);
lean_inc_ref(v_name_821_);
lean_dec_ref_known(v_host_816_, 1);
v___y_799_ = v___y_814_;
v_port_800_ = v_port_817_;
v___y_801_ = v___y_815_;
v___y_802_ = v___y_818_;
v___y_803_ = v___y_820_;
v___y_804_ = v___y_819_;
v___y_805_ = v_name_821_;
goto v___jp_798_;
}
case 1:
{
lean_object* v_ipv4_822_; lean_object* v___x_823_; 
v_ipv4_822_ = lean_ctor_get(v_host_816_, 0);
lean_inc_ref(v_ipv4_822_);
lean_dec_ref_known(v_host_816_, 1);
v___x_823_ = lean_uv_ntop_v4(v_ipv4_822_);
lean_dec_ref(v_ipv4_822_);
v___y_799_ = v___y_814_;
v_port_800_ = v_port_817_;
v___y_801_ = v___y_815_;
v___y_802_ = v___y_818_;
v___y_803_ = v___y_820_;
v___y_804_ = v___y_819_;
v___y_805_ = v___x_823_;
goto v___jp_798_;
}
default: 
{
lean_object* v_ipv6_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_ipv6_824_ = lean_ctor_get(v_host_816_, 0);
lean_inc_ref(v_ipv6_824_);
lean_dec_ref_known(v_host_816_, 1);
v___x_825_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_826_ = lean_uv_ntop_v6(v_ipv6_824_);
lean_dec_ref(v_ipv6_824_);
v___x_827_ = lean_string_append(v___x_825_, v___x_826_);
lean_dec_ref(v___x_826_);
v___x_828_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_829_ = lean_string_append(v___x_827_, v___x_828_);
v___y_799_ = v___y_814_;
v_port_800_ = v_port_817_;
v___y_801_ = v___y_815_;
v___y_802_ = v___y_818_;
v___y_803_ = v___y_820_;
v___y_804_ = v___y_819_;
v___y_805_ = v___x_829_;
goto v___jp_798_;
}
}
}
v___jp_830_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_840_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_841_ = lean_string_append(v___y_835_, v___x_840_);
v___x_842_ = lean_string_append(v___x_841_, v___y_832_);
lean_dec_ref(v___y_832_);
v___x_843_ = lean_string_append(v___x_842_, v___y_831_);
lean_dec_ref(v___y_831_);
v___x_844_ = lean_string_append(v___x_843_, v___y_836_);
lean_dec_ref(v___y_836_);
v___x_845_ = lean_string_append(v___x_844_, v___y_839_);
lean_dec_ref(v___y_839_);
v___y_773_ = v___y_833_;
v___y_774_ = v___y_834_;
v___y_775_ = v___y_837_;
v___y_776_ = v___y_838_;
v___y_777_ = v___x_845_;
goto v___jp_772_;
}
v___jp_846_:
{
lean_object* v_queryPart_856_; 
v_queryPart_856_ = l_Std_Http_URI_Query_formatOption(v___y_847_);
if (lean_obj_tag(v___y_848_) == 0)
{
lean_object* v___x_857_; 
v___x_857_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_831_ = v___y_855_;
v___y_832_ = v___y_849_;
v___y_833_ = v___y_850_;
v___y_834_ = v___y_852_;
v___y_835_ = v___y_851_;
v___y_836_ = v_queryPart_856_;
v___y_837_ = v___y_853_;
v___y_838_ = v___y_854_;
v___y_839_ = v___x_857_;
goto v___jp_830_;
}
else
{
lean_object* v_val_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_val_858_ = lean_ctor_get(v___y_848_, 0);
lean_inc(v_val_858_);
lean_dec_ref_known(v___y_848_, 1);
v___x_859_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__16));
v___x_860_ = l_Std_Http_URI_EncodedFragment_encode(v_val_858_);
lean_dec(v_val_858_);
v___x_861_ = lean_string_from_utf8_unchecked(v___x_860_);
v___x_862_ = lean_string_append(v___x_859_, v___x_861_);
lean_dec_ref(v___x_861_);
v___y_831_ = v___y_855_;
v___y_832_ = v___y_849_;
v___y_833_ = v___y_850_;
v___y_834_ = v___y_852_;
v___y_835_ = v___y_851_;
v___y_836_ = v_queryPart_856_;
v___y_837_ = v___y_853_;
v___y_838_ = v___y_854_;
v___y_839_ = v___x_862_;
goto v___jp_830_;
}
}
v___jp_863_:
{
lean_object* v_segments_873_; uint8_t v_absolute_874_; lean_object* v___x_875_; lean_object* v___x_876_; size_t v_sz_877_; size_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v_result_881_; 
v_segments_873_ = lean_ctor_get(v___y_869_, 0);
lean_inc_ref(v_segments_873_);
v_absolute_874_ = lean_ctor_get_uint8(v___y_869_, sizeof(void*)*1);
lean_dec_ref(v___y_869_);
v___x_875_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_876_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_877_ = lean_array_size(v_segments_873_);
v___x_878_ = ((size_t)0ULL);
v___x_879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_876_, v___f_739_, v_sz_877_, v___x_878_, v_segments_873_);
v___x_880_ = lean_array_to_list(v___x_879_);
v_result_881_ = l_String_intercalate(v___x_875_, v___x_880_);
if (v_absolute_874_ == 0)
{
v___y_847_ = v___y_864_;
v___y_848_ = v___y_865_;
v___y_849_ = v___y_872_;
v___y_850_ = v___y_866_;
v___y_851_ = v___y_868_;
v___y_852_ = v___y_867_;
v___y_853_ = v___y_870_;
v___y_854_ = v___y_871_;
v___y_855_ = v_result_881_;
goto v___jp_846_;
}
else
{
lean_object* v___x_882_; 
v___x_882_ = lean_string_append(v___x_875_, v_result_881_);
lean_dec_ref(v_result_881_);
v___y_847_ = v___y_864_;
v___y_848_ = v___y_865_;
v___y_849_ = v___y_872_;
v___y_850_ = v___y_866_;
v___y_851_ = v___y_868_;
v___y_852_ = v___y_867_;
v___y_853_ = v___y_870_;
v___y_854_ = v___y_871_;
v___y_855_ = v___x_882_;
goto v___jp_846_;
}
}
v___jp_883_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = lean_string_append(v___y_889_, v___y_893_);
lean_dec_ref(v___y_893_);
v___x_897_ = lean_string_append(v___x_896_, v___y_895_);
lean_dec_ref(v___y_895_);
lean_inc_ref(v___y_892_);
v___x_898_ = lean_string_append(v___y_892_, v___x_897_);
lean_dec_ref(v___x_897_);
v___y_864_ = v___y_884_;
v___y_865_ = v___y_885_;
v___y_866_ = v___y_886_;
v___y_867_ = v___y_888_;
v___y_868_ = v___y_887_;
v___y_869_ = v___y_890_;
v___y_870_ = v___y_891_;
v___y_871_ = v___y_894_;
v___y_872_ = v___x_898_;
goto v___jp_863_;
}
v___jp_899_:
{
switch(lean_obj_tag(v_port_903_))
{
case 0:
{
lean_object* v___x_912_; 
v___x_912_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_884_ = v___y_900_;
v___y_885_ = v___y_901_;
v___y_886_ = v___y_902_;
v___y_887_ = v___y_906_;
v___y_888_ = v___y_905_;
v___y_889_ = v___y_904_;
v___y_890_ = v___y_907_;
v___y_891_ = v___y_909_;
v___y_892_ = v___y_908_;
v___y_893_ = v___y_911_;
v___y_894_ = v___y_910_;
v___y_895_ = v___x_912_;
goto v___jp_883_;
}
case 1:
{
lean_object* v___x_913_; 
v___x_913_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___y_884_ = v___y_900_;
v___y_885_ = v___y_901_;
v___y_886_ = v___y_902_;
v___y_887_ = v___y_906_;
v___y_888_ = v___y_905_;
v___y_889_ = v___y_904_;
v___y_890_ = v___y_907_;
v___y_891_ = v___y_909_;
v___y_892_ = v___y_908_;
v___y_893_ = v___y_911_;
v___y_894_ = v___y_910_;
v___y_895_ = v___x_913_;
goto v___jp_883_;
}
default: 
{
uint16_t v_port_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_port_914_ = lean_ctor_get_uint16(v_port_903_, 0);
lean_dec_ref_known(v_port_903_, 0);
v___x_915_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_916_ = lean_uint16_to_nat(v_port_914_);
v___x_917_ = l_Nat_reprFast(v___x_916_);
v___x_918_ = lean_string_append(v___x_915_, v___x_917_);
lean_dec_ref(v___x_917_);
v___y_884_ = v___y_900_;
v___y_885_ = v___y_901_;
v___y_886_ = v___y_902_;
v___y_887_ = v___y_906_;
v___y_888_ = v___y_905_;
v___y_889_ = v___y_904_;
v___y_890_ = v___y_907_;
v___y_891_ = v___y_909_;
v___y_892_ = v___y_908_;
v___y_893_ = v___y_911_;
v___y_894_ = v___y_910_;
v___y_895_ = v___x_918_;
goto v___jp_883_;
}
}
}
v___jp_919_:
{
switch(lean_obj_tag(v_host_925_))
{
case 0:
{
lean_object* v_name_932_; 
v_name_932_ = lean_ctor_get(v_host_925_, 0);
lean_inc_ref(v_name_932_);
lean_dec_ref_known(v_host_925_, 1);
v___y_900_ = v___y_920_;
v___y_901_ = v___y_921_;
v___y_902_ = v___y_922_;
v_port_903_ = v_port_926_;
v___y_904_ = v___y_931_;
v___y_905_ = v___y_924_;
v___y_906_ = v___y_923_;
v___y_907_ = v___y_927_;
v___y_908_ = v___y_929_;
v___y_909_ = v___y_928_;
v___y_910_ = v___y_930_;
v___y_911_ = v_name_932_;
goto v___jp_899_;
}
case 1:
{
lean_object* v_ipv4_933_; lean_object* v___x_934_; 
v_ipv4_933_ = lean_ctor_get(v_host_925_, 0);
lean_inc_ref(v_ipv4_933_);
lean_dec_ref_known(v_host_925_, 1);
v___x_934_ = lean_uv_ntop_v4(v_ipv4_933_);
lean_dec_ref(v_ipv4_933_);
v___y_900_ = v___y_920_;
v___y_901_ = v___y_921_;
v___y_902_ = v___y_922_;
v_port_903_ = v_port_926_;
v___y_904_ = v___y_931_;
v___y_905_ = v___y_924_;
v___y_906_ = v___y_923_;
v___y_907_ = v___y_927_;
v___y_908_ = v___y_929_;
v___y_909_ = v___y_928_;
v___y_910_ = v___y_930_;
v___y_911_ = v___x_934_;
goto v___jp_899_;
}
default: 
{
lean_object* v_ipv6_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_ipv6_935_ = lean_ctor_get(v_host_925_, 0);
lean_inc_ref(v_ipv6_935_);
lean_dec_ref_known(v_host_925_, 1);
v___x_936_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__18));
v___x_937_ = lean_uv_ntop_v6(v_ipv6_935_);
lean_dec_ref(v_ipv6_935_);
v___x_938_ = lean_string_append(v___x_936_, v___x_937_);
lean_dec_ref(v___x_937_);
v___x_939_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__19));
v___x_940_ = lean_string_append(v___x_938_, v___x_939_);
v___y_900_ = v___y_920_;
v___y_901_ = v___y_921_;
v___y_902_ = v___y_922_;
v_port_903_ = v_port_926_;
v___y_904_ = v___y_931_;
v___y_905_ = v___y_924_;
v___y_906_ = v___y_923_;
v___y_907_ = v___y_927_;
v___y_908_ = v___y_929_;
v___y_909_ = v___y_928_;
v___y_910_ = v___y_930_;
v___y_911_ = v___x_940_;
goto v___jp_899_;
}
}
}
v___jp_941_:
{
lean_object* v_queryStr_948_; lean_object* v___x_949_; 
v_queryStr_948_ = l_Std_Http_URI_Query_formatOption(v___y_942_);
v___x_949_ = lean_string_append(v___y_947_, v_queryStr_948_);
lean_dec_ref(v_queryStr_948_);
v___y_773_ = v___y_943_;
v___y_774_ = v___y_944_;
v___y_775_ = v___y_945_;
v___y_776_ = v___y_946_;
v___y_777_ = v___x_949_;
goto v___jp_772_;
}
v___jp_950_:
{
lean_object* v_data_952_; lean_object* v_size_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_data_952_ = lean_ctor_get(v_buffer_741_, 0);
lean_inc_ref(v_data_952_);
v_size_953_ = lean_ctor_get(v_buffer_741_, 1);
lean_inc(v_size_953_);
lean_dec_ref(v_buffer_741_);
v___x_954_ = lean_string_to_utf8(v___y_951_);
lean_inc_ref(v___x_954_);
v___x_955_ = lean_array_push(v_data_952_, v___x_954_);
v___x_956_ = lean_byte_array_size(v___x_954_);
lean_dec_ref(v___x_954_);
v___x_957_ = lean_nat_add(v_size_953_, v___x_956_);
lean_dec(v_size_953_);
v___x_958_ = ((lean_object*)(l_Std_Http_Request_instEncodeV11Head___lam__3___closed__2));
v___x_959_ = lean_array_push(v___x_955_, v___x_958_);
v___x_960_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__3___closed__3);
v___x_961_ = lean_nat_add(v___x_957_, v___x_960_);
lean_dec(v___x_957_);
switch(lean_obj_tag(v_uri_745_))
{
case 0:
{
lean_object* v_path_962_; lean_object* v_query_963_; lean_object* v_segments_964_; uint8_t v_absolute_965_; lean_object* v___x_966_; lean_object* v___x_967_; size_t v_sz_968_; size_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v_result_972_; 
lean_dec_ref(v___f_739_);
v_path_962_ = lean_ctor_get(v_uri_745_, 0);
lean_inc_ref(v_path_962_);
v_query_963_ = lean_ctor_get(v_uri_745_, 1);
lean_inc(v_query_963_);
lean_dec_ref_known(v_uri_745_, 2);
v_segments_964_ = lean_ctor_get(v_path_962_, 0);
lean_inc_ref(v_segments_964_);
v_absolute_965_ = lean_ctor_get_uint8(v_path_962_, sizeof(void*)*1);
lean_dec_ref(v_path_962_);
v___x_966_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__17));
v___x_967_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__10));
v_sz_968_ = lean_array_size(v_segments_964_);
v___x_969_ = ((size_t)0ULL);
v___x_970_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_967_, v___f_740_, v_sz_968_, v___x_969_, v_segments_964_);
v___x_971_ = lean_array_to_list(v___x_970_);
v_result_972_ = l_String_intercalate(v___x_966_, v___x_971_);
if (v_absolute_965_ == 0)
{
v___y_942_ = v_query_963_;
v___y_943_ = v___x_958_;
v___y_944_ = v___x_960_;
v___y_945_ = v___x_961_;
v___y_946_ = v___x_959_;
v___y_947_ = v_result_972_;
goto v___jp_941_;
}
else
{
lean_object* v___x_973_; 
v___x_973_ = lean_string_append(v___x_966_, v_result_972_);
lean_dec_ref(v_result_972_);
v___y_942_ = v_query_963_;
v___y_943_ = v___x_958_;
v___y_944_ = v___x_960_;
v___y_945_ = v___x_961_;
v___y_946_ = v___x_959_;
v___y_947_ = v___x_973_;
goto v___jp_941_;
}
}
case 1:
{
lean_object* v_uri_974_; lean_object* v_authority_975_; 
lean_dec_ref(v___f_740_);
v_uri_974_ = lean_ctor_get(v_uri_745_, 0);
lean_inc_ref(v_uri_974_);
lean_dec_ref_known(v_uri_745_, 1);
v_authority_975_ = lean_ctor_get(v_uri_974_, 1);
if (lean_obj_tag(v_authority_975_) == 0)
{
lean_object* v_scheme_976_; lean_object* v_path_977_; lean_object* v_query_978_; lean_object* v_fragment_979_; lean_object* v___x_980_; 
v_scheme_976_ = lean_ctor_get(v_uri_974_, 0);
lean_inc_ref(v_scheme_976_);
v_path_977_ = lean_ctor_get(v_uri_974_, 2);
lean_inc_ref(v_path_977_);
v_query_978_ = lean_ctor_get(v_uri_974_, 3);
lean_inc(v_query_978_);
v_fragment_979_ = lean_ctor_get(v_uri_974_, 4);
lean_inc(v_fragment_979_);
lean_dec_ref(v_uri_974_);
v___x_980_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_864_ = v_query_978_;
v___y_865_ = v_fragment_979_;
v___y_866_ = v___x_958_;
v___y_867_ = v___x_960_;
v___y_868_ = v_scheme_976_;
v___y_869_ = v_path_977_;
v___y_870_ = v___x_961_;
v___y_871_ = v___x_959_;
v___y_872_ = v___x_980_;
goto v___jp_863_;
}
else
{
lean_object* v_val_981_; lean_object* v_scheme_982_; lean_object* v_path_983_; lean_object* v_query_984_; lean_object* v_fragment_985_; lean_object* v_userInfo_986_; lean_object* v_host_987_; lean_object* v_port_988_; lean_object* v___x_989_; 
v_val_981_ = lean_ctor_get(v_authority_975_, 0);
lean_inc(v_val_981_);
v_scheme_982_ = lean_ctor_get(v_uri_974_, 0);
lean_inc_ref(v_scheme_982_);
v_path_983_ = lean_ctor_get(v_uri_974_, 2);
lean_inc_ref(v_path_983_);
v_query_984_ = lean_ctor_get(v_uri_974_, 3);
lean_inc(v_query_984_);
v_fragment_985_ = lean_ctor_get(v_uri_974_, 4);
lean_inc(v_fragment_985_);
lean_dec_ref(v_uri_974_);
v_userInfo_986_ = lean_ctor_get(v_val_981_, 0);
lean_inc(v_userInfo_986_);
v_host_987_ = lean_ctor_get(v_val_981_, 1);
lean_inc_ref(v_host_987_);
v_port_988_ = lean_ctor_get(v_val_981_, 2);
lean_inc(v_port_988_);
lean_dec(v_val_981_);
v___x_989_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__21));
if (lean_obj_tag(v_userInfo_986_) == 0)
{
lean_object* v___x_990_; 
v___x_990_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_920_ = v_query_984_;
v___y_921_ = v_fragment_985_;
v___y_922_ = v___x_958_;
v___y_923_ = v_scheme_982_;
v___y_924_ = v___x_960_;
v_host_925_ = v_host_987_;
v_port_926_ = v_port_988_;
v___y_927_ = v_path_983_;
v___y_928_ = v___x_961_;
v___y_929_ = v___x_989_;
v___y_930_ = v___x_959_;
v___y_931_ = v___x_990_;
goto v___jp_919_;
}
else
{
lean_object* v_val_991_; lean_object* v_password_992_; 
v_val_991_ = lean_ctor_get(v_userInfo_986_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v_userInfo_986_, 1);
v_password_992_ = lean_ctor_get(v_val_991_, 1);
if (lean_obj_tag(v_password_992_) == 0)
{
lean_object* v_username_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_username_993_ = lean_ctor_get(v_val_991_, 0);
lean_inc_ref(v_username_993_);
lean_dec(v_val_991_);
v___x_994_ = lean_string_from_utf8_unchecked(v_username_993_);
v___x_995_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_996_ = lean_string_append(v___x_994_, v___x_995_);
v___y_920_ = v_query_984_;
v___y_921_ = v_fragment_985_;
v___y_922_ = v___x_958_;
v___y_923_ = v_scheme_982_;
v___y_924_ = v___x_960_;
v_host_925_ = v_host_987_;
v_port_926_ = v_port_988_;
v___y_927_ = v_path_983_;
v___y_928_ = v___x_961_;
v___y_929_ = v___x_989_;
v___y_930_ = v___x_959_;
v___y_931_ = v___x_996_;
goto v___jp_919_;
}
else
{
lean_object* v_username_997_; lean_object* v_val_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_inc_ref(v_password_992_);
v_username_997_ = lean_ctor_get(v_val_991_, 0);
lean_inc_ref(v_username_997_);
lean_dec(v_val_991_);
v_val_998_ = lean_ctor_get(v_password_992_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v_password_992_, 1);
v___x_999_ = lean_string_from_utf8_unchecked(v_username_997_);
v___x_1000_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_1001_ = lean_string_append(v___x_999_, v___x_1000_);
v___x_1002_ = lean_string_from_utf8_unchecked(v_val_998_);
v___x_1003_ = lean_string_append(v___x_1001_, v___x_1002_);
lean_dec_ref(v___x_1002_);
v___x_1004_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_1005_ = lean_string_append(v___x_1003_, v___x_1004_);
v___y_920_ = v_query_984_;
v___y_921_ = v_fragment_985_;
v___y_922_ = v___x_958_;
v___y_923_ = v_scheme_982_;
v___y_924_ = v___x_960_;
v_host_925_ = v_host_987_;
v_port_926_ = v_port_988_;
v___y_927_ = v_path_983_;
v___y_928_ = v___x_961_;
v___y_929_ = v___x_989_;
v___y_930_ = v___x_959_;
v___y_931_ = v___x_1005_;
goto v___jp_919_;
}
}
}
}
case 2:
{
lean_object* v_authority_1006_; lean_object* v_userInfo_1007_; 
lean_dec_ref(v___f_740_);
lean_dec_ref(v___f_739_);
v_authority_1006_ = lean_ctor_get(v_uri_745_, 0);
lean_inc_ref(v_authority_1006_);
lean_dec_ref_known(v_uri_745_, 1);
v_userInfo_1007_ = lean_ctor_get(v_authority_1006_, 0);
if (lean_obj_tag(v_userInfo_1007_) == 0)
{
lean_object* v_host_1008_; lean_object* v_port_1009_; lean_object* v___x_1010_; 
v_host_1008_ = lean_ctor_get(v_authority_1006_, 1);
lean_inc_ref(v_host_1008_);
v_port_1009_ = lean_ctor_get(v_authority_1006_, 2);
lean_inc(v_port_1009_);
lean_dec_ref(v_authority_1006_);
v___x_1010_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__3));
v___y_814_ = v___x_958_;
v___y_815_ = v___x_960_;
v_host_816_ = v_host_1008_;
v_port_817_ = v_port_1009_;
v___y_818_ = v___x_961_;
v___y_819_ = v___x_959_;
v___y_820_ = v___x_1010_;
goto v___jp_813_;
}
else
{
lean_object* v_val_1011_; lean_object* v_password_1012_; 
v_val_1011_ = lean_ctor_get(v_userInfo_1007_, 0);
lean_inc(v_val_1011_);
v_password_1012_ = lean_ctor_get(v_val_1011_, 1);
if (lean_obj_tag(v_password_1012_) == 0)
{
lean_object* v_host_1013_; lean_object* v_port_1014_; lean_object* v_username_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_host_1013_ = lean_ctor_get(v_authority_1006_, 1);
lean_inc_ref(v_host_1013_);
v_port_1014_ = lean_ctor_get(v_authority_1006_, 2);
lean_inc(v_port_1014_);
lean_dec_ref(v_authority_1006_);
v_username_1015_ = lean_ctor_get(v_val_1011_, 0);
lean_inc_ref(v_username_1015_);
lean_dec(v_val_1011_);
v___x_1016_ = lean_string_from_utf8_unchecked(v_username_1015_);
v___x_1017_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_1018_ = lean_string_append(v___x_1016_, v___x_1017_);
v___y_814_ = v___x_958_;
v___y_815_ = v___x_960_;
v_host_816_ = v_host_1013_;
v_port_817_ = v_port_1014_;
v___y_818_ = v___x_961_;
v___y_819_ = v___x_959_;
v___y_820_ = v___x_1018_;
goto v___jp_813_;
}
else
{
lean_object* v_host_1019_; lean_object* v_port_1020_; lean_object* v_username_1021_; lean_object* v_val_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_inc_ref(v_password_1012_);
v_host_1019_ = lean_ctor_get(v_authority_1006_, 1);
lean_inc_ref(v_host_1019_);
v_port_1020_ = lean_ctor_get(v_authority_1006_, 2);
lean_inc(v_port_1020_);
lean_dec_ref(v_authority_1006_);
v_username_1021_ = lean_ctor_get(v_val_1011_, 0);
lean_inc_ref(v_username_1021_);
lean_dec(v_val_1011_);
v_val_1022_ = lean_ctor_get(v_password_1012_, 0);
lean_inc(v_val_1022_);
lean_dec_ref_known(v_password_1012_, 1);
v___x_1023_ = lean_string_from_utf8_unchecked(v_username_1021_);
v___x_1024_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__15));
v___x_1025_ = lean_string_append(v___x_1023_, v___x_1024_);
v___x_1026_ = lean_string_from_utf8_unchecked(v_val_1022_);
v___x_1027_ = lean_string_append(v___x_1025_, v___x_1026_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__22));
v___x_1029_ = lean_string_append(v___x_1027_, v___x_1028_);
v___y_814_ = v___x_958_;
v___y_815_ = v___x_960_;
v_host_816_ = v_host_1019_;
v_port_817_ = v_port_1020_;
v___y_818_ = v___x_961_;
v___y_819_ = v___x_959_;
v___y_820_ = v___x_1029_;
goto v___jp_813_;
}
}
}
default: 
{
lean_object* v___x_1030_; 
lean_dec_ref(v___f_740_);
lean_dec_ref(v___f_739_);
v___x_1030_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__4___closed__23));
v___y_773_ = v___x_958_;
v___y_774_ = v___x_960_;
v___y_775_ = v___x_961_;
v___y_776_ = v___x_959_;
v___y_777_ = v___x_1030_;
goto v___jp_772_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__0(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; 
v___x_1076_ = l_Std_Http_Headers_empty;
v___x_1077_ = lean_box(3);
v___x_1078_ = 1;
v___x_1079_ = 8;
v___x_1080_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_1080_, 0, v___x_1077_);
lean_ctor_set(v___x_1080_, 1, v___x_1076_);
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*2, v___x_1079_);
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*2 + 1, v___x_1078_);
return v___x_1080_;
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__1(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = l_Std_Http_Extensions_empty;
v___x_1082_ = lean_obj_once(&l_Std_Http_Request_new___closed__0, &l_Std_Http_Request_new___closed__0_once, _init_l_Std_Http_Request_new___closed__0);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v___x_1081_);
return v___x_1083_;
}
}
static lean_object* _init_l_Std_Http_Request_new(void){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_obj_once(&l_Std_Http_Request_new___closed__1, &l_Std_Http_Request_new___closed__1_once, _init_l_Std_Http_Request_new___closed__1);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method(lean_object* v_builder_1085_, uint8_t v_method_1086_){
_start:
{
lean_object* v_line_1087_; lean_object* v_extensions_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1105_; 
v_line_1087_ = lean_ctor_get(v_builder_1085_, 0);
v_extensions_1088_ = lean_ctor_get(v_builder_1085_, 1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_builder_1085_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1090_ = v_builder_1085_;
v_isShared_1091_ = v_isSharedCheck_1105_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_extensions_1088_);
lean_inc(v_line_1087_);
lean_dec(v_builder_1085_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1105_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
uint8_t v_version_1092_; lean_object* v_uri_1093_; lean_object* v_headers_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1104_; 
v_version_1092_ = lean_ctor_get_uint8(v_line_1087_, sizeof(void*)*2 + 1);
v_uri_1093_ = lean_ctor_get(v_line_1087_, 0);
v_headers_1094_ = lean_ctor_get(v_line_1087_, 1);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_line_1087_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1096_ = v_line_1087_;
v_isShared_1097_ = v_isSharedCheck_1104_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_headers_1094_);
lean_inc(v_uri_1093_);
lean_dec(v_line_1087_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1104_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_uri_1093_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_headers_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1103_, sizeof(void*)*2 + 1, v_version_1092_);
v___x_1099_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1101_; 
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*2, v_method_1086_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1099_);
v___x_1101_ = v___x_1090_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_extensions_1088_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method___boxed(lean_object* v_builder_1106_, lean_object* v_method_1107_){
_start:
{
uint8_t v_method_boxed_1108_; lean_object* v_res_1109_; 
v_method_boxed_1108_ = lean_unbox(v_method_1107_);
v_res_1109_ = l_Std_Http_Request_Builder_method(v_builder_1106_, v_method_boxed_1108_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version(lean_object* v_builder_1110_, uint8_t v_version_1111_){
_start:
{
lean_object* v_line_1112_; lean_object* v_extensions_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1130_; 
v_line_1112_ = lean_ctor_get(v_builder_1110_, 0);
v_extensions_1113_ = lean_ctor_get(v_builder_1110_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_builder_1110_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1115_ = v_builder_1110_;
v_isShared_1116_ = v_isSharedCheck_1130_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_extensions_1113_);
lean_inc(v_line_1112_);
lean_dec(v_builder_1110_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1130_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
uint8_t v_method_1117_; lean_object* v_uri_1118_; lean_object* v_headers_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1129_; 
v_method_1117_ = lean_ctor_get_uint8(v_line_1112_, sizeof(void*)*2);
v_uri_1118_ = lean_ctor_get(v_line_1112_, 0);
v_headers_1119_ = lean_ctor_get(v_line_1112_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_line_1112_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1121_ = v_line_1112_;
v_isShared_1122_ = v_isSharedCheck_1129_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_headers_1119_);
lean_inc(v_uri_1118_);
lean_dec(v_line_1112_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1129_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_uri_1118_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_headers_1119_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, sizeof(void*)*2, v_method_1117_);
v___x_1124_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1126_; 
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*2 + 1, v_version_1111_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1124_);
v___x_1126_ = v___x_1115_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_extensions_1113_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version___boxed(lean_object* v_builder_1131_, lean_object* v_version_1132_){
_start:
{
uint8_t v_version_boxed_1133_; lean_object* v_res_1134_; 
v_version_boxed_1133_ = lean_unbox(v_version_1132_);
v_res_1134_ = l_Std_Http_Request_Builder_version(v_builder_1131_, v_version_boxed_1133_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri(lean_object* v_builder_1135_, lean_object* v_uri_1136_){
_start:
{
lean_object* v_line_1137_; lean_object* v_extensions_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1156_; 
v_line_1137_ = lean_ctor_get(v_builder_1135_, 0);
v_extensions_1138_ = lean_ctor_get(v_builder_1135_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_builder_1135_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1140_ = v_builder_1135_;
v_isShared_1141_ = v_isSharedCheck_1156_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_extensions_1138_);
lean_inc(v_line_1137_);
lean_dec(v_builder_1135_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1156_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
uint8_t v_method_1142_; uint8_t v_version_1143_; lean_object* v_headers_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1154_; 
v_method_1142_ = lean_ctor_get_uint8(v_line_1137_, sizeof(void*)*2);
v_version_1143_ = lean_ctor_get_uint8(v_line_1137_, sizeof(void*)*2 + 1);
v_headers_1144_ = lean_ctor_get(v_line_1137_, 1);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_line_1137_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v_line_1137_, 0);
lean_dec(v_unused_1155_);
v___x_1146_ = v_line_1137_;
v_isShared_1147_ = v_isSharedCheck_1154_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_headers_1144_);
lean_dec(v_line_1137_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1154_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v_uri_1136_);
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_uri_1136_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_headers_1144_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, sizeof(void*)*2, v_method_1142_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, sizeof(void*)*2 + 1, v_version_1143_);
v___x_1149_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1151_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1149_);
v___x_1151_ = v___x_1140_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_extensions_1138_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(lean_object* v_msg_1157_){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = l_Std_Http_instInhabitedRequestTarget_default;
v___x_1159_ = lean_panic_fn_borrowed(v___x_1158_, v_msg_1157_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___lam__0(lean_object* v___x_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_pos_1166_; lean_object* v_array_1167_; lean_object* v_idx_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v_pos_1166_ = lean_ctor_get(v___x_1165_, 0);
v_array_1167_ = lean_ctor_get(v_pos_1166_, 0);
v_idx_1168_ = lean_ctor_get(v_pos_1166_, 1);
v___x_1169_ = lean_byte_array_size(v_array_1167_);
v___x_1170_ = lean_nat_dec_lt(v_idx_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
return v___x_1165_;
}
else
{
lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1178_; 
lean_inc(v_pos_1166_);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; lean_object* v_unused_1180_; 
v_unused_1179_ = lean_ctor_get(v___x_1165_, 1);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v___x_1165_, 0);
lean_dec(v_unused_1180_);
v___x_1172_ = v___x_1165_;
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
else
{
lean_dec(v___x_1165_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1174_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___lam__0___closed__1));
if (v_isShared_1173_ == 0)
{
lean_ctor_set_tag(v___x_1172_, 1);
lean_ctor_set(v___x_1172_, 1, v___x_1174_);
v___x_1176_ = v___x_1172_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_pos_1166_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
else
{
return v___x_1165_;
}
}
}
static lean_object* _init_l_Std_Http_Request_Builder_uri_x21___closed__5(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1194_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__4));
v___x_1195_ = lean_unsigned_to_nat(12u);
v___x_1196_ = lean_unsigned_to_nat(45u);
v___x_1197_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__3));
v___x_1198_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__2));
v___x_1199_ = l_mkPanicMessageWithDecl(v___x_1198_, v___x_1197_, v___x_1196_, v___x_1195_, v___x_1194_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21(lean_object* v_builder_1200_, lean_object* v_uri_1201_){
_start:
{
lean_object* v___y_1203_; lean_object* v___f_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___f_1224_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__1));
v___x_1225_ = lean_string_to_utf8(v_uri_1201_);
v___x_1226_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1224_, v___x_1225_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec_ref_known(v___x_1226_, 1);
v___x_1227_ = lean_obj_once(&l_Std_Http_Request_Builder_uri_x21___closed__5, &l_Std_Http_Request_Builder_uri_x21___closed__5_once, _init_l_Std_Http_Request_Builder_uri_x21___closed__5);
v___x_1228_ = l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(v___x_1227_);
v___y_1203_ = v___x_1228_;
goto v___jp_1202_;
}
else
{
lean_object* v_a_1229_; 
v_a_1229_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1226_, 1);
v___y_1203_ = v_a_1229_;
goto v___jp_1202_;
}
v___jp_1202_:
{
lean_object* v_line_1204_; lean_object* v_extensions_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1223_; 
v_line_1204_ = lean_ctor_get(v_builder_1200_, 0);
v_extensions_1205_ = lean_ctor_get(v_builder_1200_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_builder_1200_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1207_ = v_builder_1200_;
v_isShared_1208_ = v_isSharedCheck_1223_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_extensions_1205_);
lean_inc(v_line_1204_);
lean_dec(v_builder_1200_);
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
lean_ctor_set(v___x_1213_, 0, v___y_1203_);
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___y_1203_);
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
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___boxed(lean_object* v_builder_1230_, lean_object* v_uri_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Std_Http_Request_Builder_uri_x21(v_builder_1230_, v_uri_1231_);
lean_dec_ref(v_uri_1231_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headers(lean_object* v_builder_1233_, lean_object* v_headers_1234_){
_start:
{
lean_object* v_line_1235_; lean_object* v_extensions_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1254_; 
v_line_1235_ = lean_ctor_get(v_builder_1233_, 0);
v_extensions_1236_ = lean_ctor_get(v_builder_1233_, 1);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_builder_1233_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1238_ = v_builder_1233_;
v_isShared_1239_ = v_isSharedCheck_1254_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_extensions_1236_);
lean_inc(v_line_1235_);
lean_dec(v_builder_1233_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1254_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
uint8_t v_method_1240_; uint8_t v_version_1241_; lean_object* v_uri_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1252_; 
v_method_1240_ = lean_ctor_get_uint8(v_line_1235_, sizeof(void*)*2);
v_version_1241_ = lean_ctor_get_uint8(v_line_1235_, sizeof(void*)*2 + 1);
v_uri_1242_ = lean_ctor_get(v_line_1235_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_line_1235_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v_line_1235_, 1);
lean_dec(v_unused_1253_);
v___x_1244_ = v_line_1235_;
v_isShared_1245_ = v_isSharedCheck_1252_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_uri_1242_);
lean_dec(v_line_1235_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1252_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v_headers_1234_);
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_uri_1242_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_headers_1234_);
lean_ctor_set_uint8(v_reuseFailAlloc_1251_, sizeof(void*)*2, v_method_1240_);
lean_ctor_set_uint8(v_reuseFailAlloc_1251_, sizeof(void*)*2 + 1, v_version_1241_);
v___x_1247_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1249_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1247_);
v___x_1249_ = v___x_1238_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_extensions_1236_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(lean_object* v_i_1255_, lean_object* v_x_1256_){
_start:
{
if (lean_obj_tag(v_x_1256_) == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = lean_mk_empty_array_with_capacity(v___x_1257_);
v___x_1259_ = lean_array_push(v___x_1258_, v_i_1255_);
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
return v___x_1260_;
}
else
{
lean_object* v_val_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1269_; 
v_val_1261_ = lean_ctor_get(v_x_1256_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_x_1256_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1263_ = v_x_1256_;
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_val_1261_);
lean_dec(v_x_1256_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1265_ = lean_array_push(v_val_1261_, v_i_1255_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1265_);
v___x_1267_ = v___x_1263_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(lean_object* v_i_1270_, lean_object* v_a_1271_, lean_object* v_x_1272_){
_start:
{
if (lean_obj_tag(v_x_1272_) == 0)
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v_val_1275_; lean_object* v___x_1276_; 
v___x_1273_ = lean_box(0);
v___x_1274_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(v_i_1270_, v___x_1273_);
v_val_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_val_1275_);
lean_dec(v___x_1274_);
v___x_1276_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1276_, 0, v_a_1271_);
lean_ctor_set(v___x_1276_, 1, v_val_1275_);
lean_ctor_set(v___x_1276_, 2, v_x_1272_);
return v___x_1276_;
}
else
{
lean_object* v_key_1277_; lean_object* v_value_1278_; lean_object* v_tail_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1294_; 
v_key_1277_ = lean_ctor_get(v_x_1272_, 0);
v_value_1278_ = lean_ctor_get(v_x_1272_, 1);
v_tail_1279_ = lean_ctor_get(v_x_1272_, 2);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_x_1272_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1281_ = v_x_1272_;
v_isShared_1282_ = v_isSharedCheck_1294_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_tail_1279_);
lean_inc(v_value_1278_);
lean_inc(v_key_1277_);
lean_dec(v_x_1272_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1294_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
uint8_t v___x_1283_; 
v___x_1283_ = lean_string_dec_eq(v_key_1277_, v_a_1271_);
if (v___x_1283_ == 0)
{
lean_object* v_tail_1284_; lean_object* v___x_1286_; 
v_tail_1284_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_1270_, v_a_1271_, v_tail_1279_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 2, v_tail_1284_);
v___x_1286_ = v___x_1281_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_key_1277_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_value_1278_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_tail_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v_val_1290_; lean_object* v___x_1292_; 
lean_dec(v_key_1277_);
v___x_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1288_, 0, v_value_1278_);
v___x_1289_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(v_i_1270_, v___x_1288_);
v_val_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_val_1290_);
lean_dec(v___x_1289_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v_val_1290_);
lean_ctor_set(v___x_1281_, 0, v_a_1271_);
v___x_1292_ = v___x_1281_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1271_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_val_1290_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v_tail_1279_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(lean_object* v_a_1295_, lean_object* v_x_1296_){
_start:
{
if (lean_obj_tag(v_x_1296_) == 0)
{
uint8_t v___x_1297_; 
v___x_1297_ = 0;
return v___x_1297_;
}
else
{
lean_object* v_key_1298_; lean_object* v_tail_1299_; uint8_t v___x_1300_; 
v_key_1298_ = lean_ctor_get(v_x_1296_, 0);
v_tail_1299_ = lean_ctor_get(v_x_1296_, 2);
v___x_1300_ = lean_string_dec_eq(v_key_1298_, v_a_1295_);
if (v___x_1300_ == 0)
{
v_x_1296_ = v_tail_1299_;
goto _start;
}
else
{
return v___x_1300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg___boxed(lean_object* v_a_1302_, lean_object* v_x_1303_){
_start:
{
uint8_t v_res_1304_; lean_object* v_r_1305_; 
v_res_1304_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1302_, v_x_1303_);
lean_dec(v_x_1303_);
lean_dec_ref(v_a_1302_);
v_r_1305_ = lean_box(v_res_1304_);
return v_r_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1306_, lean_object* v_x_1307_){
_start:
{
if (lean_obj_tag(v_x_1307_) == 0)
{
return v_x_1306_;
}
else
{
lean_object* v_key_1308_; lean_object* v_value_1309_; lean_object* v_tail_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1333_; 
v_key_1308_ = lean_ctor_get(v_x_1307_, 0);
v_value_1309_ = lean_ctor_get(v_x_1307_, 1);
v_tail_1310_ = lean_ctor_get(v_x_1307_, 2);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_x_1307_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1312_ = v_x_1307_;
v_isShared_1313_ = v_isSharedCheck_1333_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_tail_1310_);
lean_inc(v_value_1309_);
lean_inc(v_key_1308_);
lean_dec(v_x_1307_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1333_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; uint64_t v___x_1315_; uint64_t v___x_1316_; uint64_t v___x_1317_; uint64_t v_fold_1318_; uint64_t v___x_1319_; uint64_t v___x_1320_; uint64_t v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; size_t v___x_1324_; size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1314_ = lean_array_get_size(v_x_1306_);
v___x_1315_ = lean_string_hash(v_key_1308_);
v___x_1316_ = 32ULL;
v___x_1317_ = lean_uint64_shift_right(v___x_1315_, v___x_1316_);
v_fold_1318_ = lean_uint64_xor(v___x_1315_, v___x_1317_);
v___x_1319_ = 16ULL;
v___x_1320_ = lean_uint64_shift_right(v_fold_1318_, v___x_1319_);
v___x_1321_ = lean_uint64_xor(v_fold_1318_, v___x_1320_);
v___x_1322_ = lean_uint64_to_usize(v___x_1321_);
v___x_1323_ = lean_usize_of_nat(v___x_1314_);
v___x_1324_ = ((size_t)1ULL);
v___x_1325_ = lean_usize_sub(v___x_1323_, v___x_1324_);
v___x_1326_ = lean_usize_land(v___x_1322_, v___x_1325_);
v___x_1327_ = lean_array_uget_borrowed(v_x_1306_, v___x_1326_);
lean_inc(v___x_1327_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 2, v___x_1327_);
v___x_1329_ = v___x_1312_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_key_1308_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_value_1309_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_array_uset(v_x_1306_, v___x_1326_, v___x_1329_);
v_x_1306_ = v___x_1330_;
v_x_1307_ = v_tail_1310_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1334_, lean_object* v_source_1335_, lean_object* v_target_1336_){
_start:
{
lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1337_ = lean_array_get_size(v_source_1335_);
v___x_1338_ = lean_nat_dec_lt(v_i_1334_, v___x_1337_);
if (v___x_1338_ == 0)
{
lean_dec_ref(v_source_1335_);
lean_dec(v_i_1334_);
return v_target_1336_;
}
else
{
lean_object* v_es_1339_; lean_object* v___x_1340_; lean_object* v_source_1341_; lean_object* v_target_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_es_1339_ = lean_array_fget(v_source_1335_, v_i_1334_);
v___x_1340_ = lean_box(0);
v_source_1341_ = lean_array_fset(v_source_1335_, v_i_1334_, v___x_1340_);
v_target_1342_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1336_, v_es_1339_);
v___x_1343_ = lean_unsigned_to_nat(1u);
v___x_1344_ = lean_nat_add(v_i_1334_, v___x_1343_);
lean_dec(v_i_1334_);
v_i_1334_ = v___x_1344_;
v_source_1335_ = v_source_1341_;
v_target_1336_ = v_target_1342_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(lean_object* v_data_1346_){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v_nbuckets_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1347_ = lean_array_get_size(v_data_1346_);
v___x_1348_ = lean_unsigned_to_nat(2u);
v_nbuckets_1349_ = lean_nat_mul(v___x_1347_, v___x_1348_);
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = lean_box(0);
v___x_1352_ = lean_mk_array(v_nbuckets_1349_, v___x_1351_);
v___x_1353_ = lean_array_propagate_mark(v_data_1346_, v___x_1352_);
v___x_1354_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v___x_1350_, v_data_1346_, v___x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(lean_object* v_i_1355_, lean_object* v_m_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v_size_1358_; lean_object* v_buckets_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1409_; 
v_size_1358_ = lean_ctor_get(v_m_1356_, 0);
v_buckets_1359_ = lean_ctor_get(v_m_1356_, 1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_m_1356_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1361_ = v_m_1356_;
v_isShared_1362_ = v_isSharedCheck_1409_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_buckets_1359_);
lean_inc(v_size_1358_);
lean_dec(v_m_1356_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1409_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; uint64_t v___x_1364_; uint64_t v___x_1365_; uint64_t v___x_1366_; uint64_t v_fold_1367_; uint64_t v___x_1368_; uint64_t v___x_1369_; uint64_t v___x_1370_; size_t v___x_1371_; size_t v___x_1372_; size_t v___x_1373_; size_t v___x_1374_; size_t v___x_1375_; lean_object* v_bkt_1376_; uint8_t v___x_1377_; 
v___x_1363_ = lean_array_get_size(v_buckets_1359_);
v___x_1364_ = lean_string_hash(v_a_1357_);
v___x_1365_ = 32ULL;
v___x_1366_ = lean_uint64_shift_right(v___x_1364_, v___x_1365_);
v_fold_1367_ = lean_uint64_xor(v___x_1364_, v___x_1366_);
v___x_1368_ = 16ULL;
v___x_1369_ = lean_uint64_shift_right(v_fold_1367_, v___x_1368_);
v___x_1370_ = lean_uint64_xor(v_fold_1367_, v___x_1369_);
v___x_1371_ = lean_uint64_to_usize(v___x_1370_);
v___x_1372_ = lean_usize_of_nat(v___x_1363_);
v___x_1373_ = ((size_t)1ULL);
v___x_1374_ = lean_usize_sub(v___x_1372_, v___x_1373_);
v___x_1375_ = lean_usize_land(v___x_1371_, v___x_1374_);
v_bkt_1376_ = lean_array_uget_borrowed(v_buckets_1359_, v___x_1375_);
v___x_1377_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1357_, v_bkt_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v_size_x27_1381_; lean_object* v___x_1382_; lean_object* v_buckets_x27_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1378_ = lean_unsigned_to_nat(1u);
v___x_1379_ = lean_mk_empty_array_with_capacity(v___x_1378_);
v___x_1380_ = lean_array_push(v___x_1379_, v_i_1355_);
v_size_x27_1381_ = lean_nat_add(v_size_1358_, v___x_1378_);
lean_dec(v_size_1358_);
lean_inc(v_bkt_1376_);
v___x_1382_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1382_, 0, v_a_1357_);
lean_ctor_set(v___x_1382_, 1, v___x_1380_);
lean_ctor_set(v___x_1382_, 2, v_bkt_1376_);
v_buckets_x27_1383_ = lean_array_uset(v_buckets_1359_, v___x_1375_, v___x_1382_);
v___x_1384_ = lean_unsigned_to_nat(4u);
v___x_1385_ = lean_nat_mul(v_size_x27_1381_, v___x_1384_);
v___x_1386_ = lean_unsigned_to_nat(3u);
v___x_1387_ = lean_nat_div(v___x_1385_, v___x_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_array_get_size(v_buckets_x27_1383_);
v___x_1389_ = lean_nat_dec_le(v___x_1387_, v___x_1388_);
lean_dec(v___x_1387_);
if (v___x_1389_ == 0)
{
lean_object* v_val_1390_; lean_object* v___x_1392_; 
v_val_1390_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_buckets_x27_1383_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 1, v_val_1390_);
lean_ctor_set(v___x_1361_, 0, v_size_x27_1381_);
v___x_1392_ = v___x_1361_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_size_x27_1381_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_val_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
else
{
lean_object* v___x_1395_; 
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 1, v_buckets_x27_1383_);
lean_ctor_set(v___x_1361_, 0, v_size_x27_1381_);
v___x_1395_ = v___x_1361_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_size_x27_1381_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_buckets_x27_1383_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
else
{
lean_object* v___x_1397_; lean_object* v_buckets_x27_1398_; lean_object* v_bkt_x27_1399_; lean_object* v___y_1401_; uint8_t v___x_1406_; 
lean_inc(v_bkt_1376_);
v___x_1397_ = lean_box(0);
v_buckets_x27_1398_ = lean_array_uset(v_buckets_1359_, v___x_1375_, v___x_1397_);
lean_inc_ref(v_a_1357_);
v_bkt_x27_1399_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_1355_, v_a_1357_, v_bkt_1376_);
v___x_1406_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1357_, v_bkt_x27_1399_);
lean_dec_ref(v_a_1357_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = lean_unsigned_to_nat(1u);
v___x_1408_ = lean_nat_sub(v_size_1358_, v___x_1407_);
lean_dec(v_size_1358_);
v___y_1401_ = v___x_1408_;
goto v___jp_1400_;
}
else
{
v___y_1401_ = v_size_1358_;
goto v___jp_1400_;
}
v___jp_1400_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = lean_array_uset(v_buckets_x27_1398_, v___x_1375_, v_bkt_x27_1399_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 1, v___x_1402_);
lean_ctor_set(v___x_1361_, 0, v___y_1401_);
v___x_1404_ = v___x_1361_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___y_1401_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header(lean_object* v_builder_1410_, lean_object* v_key_1411_, lean_object* v_value_1412_){
_start:
{
lean_object* v_line_1413_; lean_object* v_headers_1414_; lean_object* v_extensions_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1446_; 
v_line_1413_ = lean_ctor_get(v_builder_1410_, 0);
lean_inc_ref(v_line_1413_);
v_headers_1414_ = lean_ctor_get(v_line_1413_, 1);
lean_inc_ref(v_headers_1414_);
v_extensions_1415_ = lean_ctor_get(v_builder_1410_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_builder_1410_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; 
v_unused_1447_ = lean_ctor_get(v_builder_1410_, 0);
lean_dec(v_unused_1447_);
v___x_1417_ = v_builder_1410_;
v_isShared_1418_ = v_isSharedCheck_1446_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_extensions_1415_);
lean_dec(v_builder_1410_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1446_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
uint8_t v_method_1419_; uint8_t v_version_1420_; lean_object* v_uri_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1444_; 
v_method_1419_ = lean_ctor_get_uint8(v_line_1413_, sizeof(void*)*2);
v_version_1420_ = lean_ctor_get_uint8(v_line_1413_, sizeof(void*)*2 + 1);
v_uri_1421_ = lean_ctor_get(v_line_1413_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_line_1413_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; 
v_unused_1445_ = lean_ctor_get(v_line_1413_, 1);
lean_dec(v_unused_1445_);
v___x_1423_ = v_line_1413_;
v_isShared_1424_ = v_isSharedCheck_1444_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_uri_1421_);
lean_dec(v_line_1413_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1444_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v_entries_1425_; lean_object* v_indexes_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1443_; 
v_entries_1425_ = lean_ctor_get(v_headers_1414_, 0);
v_indexes_1426_ = lean_ctor_get(v_headers_1414_, 1);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_headers_1414_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1428_ = v_headers_1414_;
v_isShared_1429_ = v_isSharedCheck_1443_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_indexes_1426_);
lean_inc(v_entries_1425_);
lean_dec(v_headers_1414_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1443_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v_i_1430_; lean_object* v___x_1431_; lean_object* v_entries_1432_; lean_object* v_indexes_1433_; lean_object* v___x_1435_; 
v_i_1430_ = lean_array_get_size(v_entries_1425_);
lean_inc_ref(v_key_1411_);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v_key_1411_);
lean_ctor_set(v___x_1431_, 1, v_value_1412_);
v_entries_1432_ = lean_array_push(v_entries_1425_, v___x_1431_);
v_indexes_1433_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1430_, v_indexes_1426_, v_key_1411_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 1, v_indexes_1433_);
lean_ctor_set(v___x_1428_, 0, v_entries_1432_);
v___x_1435_ = v___x_1428_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_entries_1432_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_indexes_1433_);
v___x_1435_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1437_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v___x_1435_);
v___x_1437_ = v___x_1423_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_uri_1421_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___x_1435_);
lean_ctor_set_uint8(v_reuseFailAlloc_1441_, sizeof(void*)*2, v_method_1419_);
lean_ctor_set_uint8(v_reuseFailAlloc_1441_, sizeof(void*)*2 + 1, v_version_1420_);
v___x_1437_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_object* v___x_1439_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1437_);
v___x_1439_ = v___x_1417_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_extensions_1415_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(lean_object* v_00_u03b2_1448_, lean_object* v_a_1449_, lean_object* v_x_1450_){
_start:
{
uint8_t v___x_1451_; 
v___x_1451_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1449_, v_x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1452_, lean_object* v_a_1453_, lean_object* v_x_1454_){
_start:
{
uint8_t v_res_1455_; lean_object* v_r_1456_; 
v_res_1455_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(v_00_u03b2_1452_, v_a_1453_, v_x_1454_);
lean_dec(v_x_1454_);
lean_dec_ref(v_a_1453_);
v_r_1456_ = lean_box(v_res_1455_);
return v_r_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1(lean_object* v_00_u03b2_1457_, lean_object* v_data_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_data_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1460_, lean_object* v_i_1461_, lean_object* v_source_1462_, lean_object* v_target_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v_i_1461_, v_source_1462_, v_target_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1466_, v_x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x21(lean_object* v_builder_1469_, lean_object* v_key_1470_, lean_object* v_value_1471_){
_start:
{
lean_object* v_line_1472_; lean_object* v_headers_1473_; lean_object* v_extensions_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1507_; 
v_line_1472_ = lean_ctor_get(v_builder_1469_, 0);
lean_inc_ref(v_line_1472_);
v_headers_1473_ = lean_ctor_get(v_line_1472_, 1);
lean_inc_ref(v_headers_1473_);
v_extensions_1474_ = lean_ctor_get(v_builder_1469_, 1);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_builder_1469_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; 
v_unused_1508_ = lean_ctor_get(v_builder_1469_, 0);
lean_dec(v_unused_1508_);
v___x_1476_ = v_builder_1469_;
v_isShared_1477_ = v_isSharedCheck_1507_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_extensions_1474_);
lean_dec(v_builder_1469_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1507_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
uint8_t v_method_1478_; uint8_t v_version_1479_; lean_object* v_uri_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1505_; 
v_method_1478_ = lean_ctor_get_uint8(v_line_1472_, sizeof(void*)*2);
v_version_1479_ = lean_ctor_get_uint8(v_line_1472_, sizeof(void*)*2 + 1);
v_uri_1480_ = lean_ctor_get(v_line_1472_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_line_1472_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v_line_1472_, 1);
lean_dec(v_unused_1506_);
v___x_1482_ = v_line_1472_;
v_isShared_1483_ = v_isSharedCheck_1505_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_uri_1480_);
lean_dec(v_line_1472_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1505_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v_entries_1484_; lean_object* v_indexes_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1504_; 
v_entries_1484_ = lean_ctor_get(v_headers_1473_, 0);
v_indexes_1485_ = lean_ctor_get(v_headers_1473_, 1);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_headers_1473_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1487_ = v_headers_1473_;
v_isShared_1488_ = v_isSharedCheck_1504_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_indexes_1485_);
lean_inc(v_entries_1484_);
lean_dec(v_headers_1473_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1504_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v_key_1489_; lean_object* v_value_1490_; lean_object* v_i_1491_; lean_object* v___x_1492_; lean_object* v_entries_1493_; lean_object* v_indexes_1494_; lean_object* v___x_1496_; 
v_key_1489_ = l_Std_Http_Header_Name_ofString_x21(v_key_1470_);
v_value_1490_ = l_Std_Http_Header_Value_ofString_x21(v_value_1471_);
v_i_1491_ = lean_array_get_size(v_entries_1484_);
lean_inc_ref(v_key_1489_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v_key_1489_);
lean_ctor_set(v___x_1492_, 1, v_value_1490_);
v_entries_1493_ = lean_array_push(v_entries_1484_, v___x_1492_);
v_indexes_1494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1491_, v_indexes_1485_, v_key_1489_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v_indexes_1494_);
lean_ctor_set(v___x_1487_, 0, v_entries_1493_);
v___x_1496_ = v___x_1487_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_entries_1493_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_indexes_1494_);
v___x_1496_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v___x_1496_);
v___x_1498_ = v___x_1482_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_uri_1480_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v___x_1496_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*2, v_method_1478_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*2 + 1, v_version_1479_);
v___x_1498_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1498_);
v___x_1500_ = v___x_1476_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_extensions_1474_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x3f(lean_object* v_builder_1509_, lean_object* v_key_1510_, lean_object* v_value_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Std_Http_Header_Name_ofString_x3f(v_key_1510_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v___x_1513_; 
lean_dec_ref(v_value_1511_);
lean_dec_ref(v_builder_1509_);
v___x_1513_ = lean_box(0);
return v___x_1513_;
}
else
{
lean_object* v_val_1514_; lean_object* v___x_1515_; 
v_val_1514_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_val_1514_);
lean_dec_ref_known(v___x_1512_, 1);
v___x_1515_ = l_Std_Http_Header_Value_ofString_x3f(v_value_1511_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v___x_1516_; 
lean_dec(v_val_1514_);
lean_dec_ref(v_builder_1509_);
v___x_1516_ = lean_box(0);
return v___x_1516_;
}
else
{
lean_object* v_line_1517_; lean_object* v_headers_1518_; lean_object* v_val_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1559_; 
v_line_1517_ = lean_ctor_get(v_builder_1509_, 0);
lean_inc_ref(v_line_1517_);
v_headers_1518_ = lean_ctor_get(v_line_1517_, 1);
lean_inc_ref(v_headers_1518_);
v_val_1519_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1521_ = v___x_1515_;
v_isShared_1522_ = v_isSharedCheck_1559_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_val_1519_);
lean_dec(v___x_1515_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1559_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v_extensions_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1557_; 
v_extensions_1523_ = lean_ctor_get(v_builder_1509_, 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_builder_1509_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; 
v_unused_1558_ = lean_ctor_get(v_builder_1509_, 0);
lean_dec(v_unused_1558_);
v___x_1525_ = v_builder_1509_;
v_isShared_1526_ = v_isSharedCheck_1557_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_extensions_1523_);
lean_dec(v_builder_1509_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1557_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
uint8_t v_method_1527_; uint8_t v_version_1528_; lean_object* v_uri_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1555_; 
v_method_1527_ = lean_ctor_get_uint8(v_line_1517_, sizeof(void*)*2);
v_version_1528_ = lean_ctor_get_uint8(v_line_1517_, sizeof(void*)*2 + 1);
v_uri_1529_ = lean_ctor_get(v_line_1517_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_line_1517_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; 
v_unused_1556_ = lean_ctor_get(v_line_1517_, 1);
lean_dec(v_unused_1556_);
v___x_1531_ = v_line_1517_;
v_isShared_1532_ = v_isSharedCheck_1555_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_uri_1529_);
lean_dec(v_line_1517_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1555_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_entries_1533_; lean_object* v_indexes_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1554_; 
v_entries_1533_ = lean_ctor_get(v_headers_1518_, 0);
v_indexes_1534_ = lean_ctor_get(v_headers_1518_, 1);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_headers_1518_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1536_ = v_headers_1518_;
v_isShared_1537_ = v_isSharedCheck_1554_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_indexes_1534_);
lean_inc(v_entries_1533_);
lean_dec(v_headers_1518_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1554_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v_i_1538_; lean_object* v___x_1539_; lean_object* v_entries_1540_; lean_object* v_indexes_1541_; lean_object* v___x_1543_; 
v_i_1538_ = lean_array_get_size(v_entries_1533_);
lean_inc(v_val_1514_);
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v_val_1514_);
lean_ctor_set(v___x_1539_, 1, v_val_1519_);
v_entries_1540_ = lean_array_push(v_entries_1533_, v___x_1539_);
v_indexes_1541_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1538_, v_indexes_1534_, v_val_1514_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 1, v_indexes_1541_);
lean_ctor_set(v___x_1536_, 0, v_entries_1540_);
v___x_1543_ = v___x_1536_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_entries_1540_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_indexes_1541_);
v___x_1543_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1545_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 1, v___x_1543_);
v___x_1545_ = v___x_1531_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_uri_1529_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v___x_1543_);
lean_ctor_set_uint8(v_reuseFailAlloc_1552_, sizeof(void*)*2, v_method_1527_);
lean_ctor_set_uint8(v_reuseFailAlloc_1552_, sizeof(void*)*2 + 1, v_version_1528_);
v___x_1545_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1547_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1545_);
v___x_1547_ = v___x_1525_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_extensions_1523_);
v___x_1547_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1549_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v___x_1547_);
v___x_1549_ = v___x_1521_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
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
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headerOpt(lean_object* v_builder_1560_, lean_object* v_key_1561_, lean_object* v_value_1562_){
_start:
{
if (lean_obj_tag(v_value_1562_) == 0)
{
lean_dec_ref(v_key_1561_);
return v_builder_1560_;
}
else
{
lean_object* v_val_1563_; lean_object* v___x_1564_; 
v_val_1563_ = lean_ctor_get(v_value_1562_, 0);
lean_inc(v_val_1563_);
lean_dec_ref_known(v_value_1562_, 1);
v___x_1564_ = l_Std_Http_Request_Builder_header(v_builder_1560_, v_key_1561_, v_val_1563_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension___redArg(lean_object* v_builder_1566_, lean_object* v_inst_1567_, lean_object* v_data_1568_){
_start:
{
lean_object* v_line_1569_; lean_object* v_extensions_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1581_; 
v_line_1569_ = lean_ctor_get(v_builder_1566_, 0);
v_extensions_1570_ = lean_ctor_get(v_builder_1566_, 1);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_builder_1566_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1572_ = v_builder_1566_;
v_isShared_1573_ = v_isSharedCheck_1581_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_extensions_1570_);
lean_inc(v_line_1569_);
lean_dec(v_builder_1566_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1581_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v_dyn_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
v_dyn_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_1574_, 0, v_inst_1567_);
lean_ctor_set(v_dyn_1574_, 1, v_data_1568_);
v___x_1575_ = ((lean_object*)(l_Std_Http_Request_Builder_extension___redArg___closed__0));
v___x_1576_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_1574_);
v___x_1577_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1575_, v___x_1576_, v_dyn_1574_, v_extensions_1570_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 1, v___x_1577_);
v___x_1579_ = v___x_1572_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_line_1569_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension(lean_object* v_00_u03b1_1582_, lean_object* v_builder_1583_, lean_object* v_inst_1584_, lean_object* v_data_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Std_Http_Request_Builder_extension___redArg(v_builder_1583_, v_inst_1584_, v_data_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object* v_builder_1587_, lean_object* v_body_1588_){
_start:
{
lean_object* v_line_1589_; lean_object* v_extensions_1590_; lean_object* v___x_1591_; 
v_line_1589_ = lean_ctor_get(v_builder_1587_, 0);
v_extensions_1590_ = lean_ctor_get(v_builder_1587_, 1);
lean_inc(v_extensions_1590_);
lean_inc_ref(v_line_1589_);
v___x_1591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1591_, 0, v_line_1589_);
lean_ctor_set(v___x_1591_, 1, v_body_1588_);
lean_ctor_set(v___x_1591_, 2, v_extensions_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg___boxed(lean_object* v_builder_1592_, lean_object* v_body_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1592_, v_body_1593_);
lean_dec_ref(v_builder_1592_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body(lean_object* v_t_1595_, lean_object* v_builder_1596_, lean_object* v_body_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1596_, v_body_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___boxed(lean_object* v_t_1599_, lean_object* v_builder_1600_, lean_object* v_body_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Std_Http_Request_Builder_body(v_t_1599_, v_builder_1600_, v_body_1601_);
lean_dec_ref(v_builder_1600_);
return v_res_1602_;
}
}
static lean_object* _init_l_Std_Http_Request_get___closed__0(void){
_start:
{
uint8_t v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1603_ = 8;
v___x_1604_ = l_Std_Http_Request_new;
v___x_1605_ = l_Std_Http_Request_Builder_method(v___x_1604_, v___x_1603_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_get(lean_object* v_uri_1606_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_obj_once(&l_Std_Http_Request_get___closed__0, &l_Std_Http_Request_get___closed__0_once, _init_l_Std_Http_Request_get___closed__0);
v___x_1608_ = l_Std_Http_Request_Builder_uri(v___x_1607_, v_uri_1606_);
return v___x_1608_;
}
}
static lean_object* _init_l_Std_Http_Request_post___closed__0(void){
_start:
{
uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = 23;
v___x_1610_ = l_Std_Http_Request_new;
v___x_1611_ = l_Std_Http_Request_Builder_method(v___x_1610_, v___x_1609_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_post(lean_object* v_uri_1612_){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = lean_obj_once(&l_Std_Http_Request_post___closed__0, &l_Std_Http_Request_post___closed__0_once, _init_l_Std_Http_Request_post___closed__0);
v___x_1614_ = l_Std_Http_Request_Builder_uri(v___x_1613_, v_uri_1612_);
return v___x_1614_;
}
}
static lean_object* _init_l_Std_Http_Request_put___closed__0(void){
_start:
{
uint8_t v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = 27;
v___x_1616_ = l_Std_Http_Request_new;
v___x_1617_ = l_Std_Http_Request_Builder_method(v___x_1616_, v___x_1615_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_put(lean_object* v_uri_1618_){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = lean_obj_once(&l_Std_Http_Request_put___closed__0, &l_Std_Http_Request_put___closed__0_once, _init_l_Std_Http_Request_put___closed__0);
v___x_1620_ = l_Std_Http_Request_Builder_uri(v___x_1619_, v_uri_1618_);
return v___x_1620_;
}
}
static lean_object* _init_l_Std_Http_Request_delete___closed__0(void){
_start:
{
uint8_t v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1621_ = 7;
v___x_1622_ = l_Std_Http_Request_new;
v___x_1623_ = l_Std_Http_Request_Builder_method(v___x_1622_, v___x_1621_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_delete(lean_object* v_uri_1624_){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = lean_obj_once(&l_Std_Http_Request_delete___closed__0, &l_Std_Http_Request_delete___closed__0_once, _init_l_Std_Http_Request_delete___closed__0);
v___x_1626_ = l_Std_Http_Request_Builder_uri(v___x_1625_, v_uri_1624_);
return v___x_1626_;
}
}
static lean_object* _init_l_Std_Http_Request_patch___closed__0(void){
_start:
{
uint8_t v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1627_ = 22;
v___x_1628_ = l_Std_Http_Request_new;
v___x_1629_ = l_Std_Http_Request_Builder_method(v___x_1628_, v___x_1627_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_patch(lean_object* v_uri_1630_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_obj_once(&l_Std_Http_Request_patch___closed__0, &l_Std_Http_Request_patch___closed__0_once, _init_l_Std_Http_Request_patch___closed__0);
v___x_1632_ = l_Std_Http_Request_Builder_uri(v___x_1631_, v_uri_1630_);
return v___x_1632_;
}
}
static lean_object* _init_l_Std_Http_Request_head___closed__0(void){
_start:
{
uint8_t v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1633_ = 9;
v___x_1634_ = l_Std_Http_Request_new;
v___x_1635_ = l_Std_Http_Request_Builder_method(v___x_1634_, v___x_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_head(lean_object* v_uri_1636_){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = lean_obj_once(&l_Std_Http_Request_head___closed__0, &l_Std_Http_Request_head___closed__0_once, _init_l_Std_Http_Request_head___closed__0);
v___x_1638_ = l_Std_Http_Request_Builder_uri(v___x_1637_, v_uri_1636_);
return v___x_1638_;
}
}
static lean_object* _init_l_Std_Http_Request_options___closed__0(void){
_start:
{
uint8_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1639_ = 20;
v___x_1640_ = l_Std_Http_Request_new;
v___x_1641_ = l_Std_Http_Request_Builder_method(v___x_1640_, v___x_1639_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_options(lean_object* v_uri_1642_){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = lean_obj_once(&l_Std_Http_Request_options___closed__0, &l_Std_Http_Request_options___closed__0_once, _init_l_Std_Http_Request_options___closed__0);
v___x_1644_ = l_Std_Http_Request_Builder_uri(v___x_1643_, v_uri_1642_);
return v___x_1644_;
}
}
static lean_object* _init_l_Std_Http_Request_connect___closed__0(void){
_start:
{
uint8_t v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1645_ = 5;
v___x_1646_ = l_Std_Http_Request_new;
v___x_1647_ = l_Std_Http_Request_Builder_method(v___x_1646_, v___x_1645_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_connect(lean_object* v_uri_1648_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = lean_obj_once(&l_Std_Http_Request_connect___closed__0, &l_Std_Http_Request_connect___closed__0_once, _init_l_Std_Http_Request_connect___closed__0);
v___x_1650_ = l_Std_Http_Request_Builder_uri(v___x_1649_, v_uri_1648_);
return v___x_1650_;
}
}
static lean_object* _init_l_Std_Http_Request_trace___closed__0(void){
_start:
{
uint8_t v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1651_ = 32;
v___x_1652_ = l_Std_Http_Request_new;
v___x_1653_ = l_Std_Http_Request_Builder_method(v___x_1652_, v___x_1651_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_trace(lean_object* v_uri_1654_){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = lean_obj_once(&l_Std_Http_Request_trace___closed__0, &l_Std_Http_Request_trace___closed__0_once, _init_l_Std_Http_Request_trace___closed__0);
v___x_1656_ = l_Std_Http_Request_Builder_uri(v___x_1655_, v_uri_1654_);
return v___x_1656_;
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
