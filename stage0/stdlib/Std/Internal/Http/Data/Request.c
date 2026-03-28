// Lean compiler output
// Module: Std.Internal.Http.Data.Request
// Imports: public import Std.Internal.Http.Data.Extensions public import Std.Internal.Http.Data.Method public import Std.Internal.Http.Data.Version public import Std.Internal.Http.Data.Headers public import Std.Internal.Http.Data.URI
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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_Http_Headers_fold___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_uv_ntop_v4(lean_object*);
lean_object* lean_uv_ntop_v6(lean_object*);
lean_object* l_Std_Http_URI_EncodedFragment_encode(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Extensions_empty;
extern lean_object* l_Std_Http_Headers_empty;
extern lean_object* l_Std_Http_instInhabitedHeaders_default;
extern lean_object* l_Std_Http_instInhabitedRequestTarget_default;
extern lean_object* l_Std_Http_instInhabitedExtensions_default;
lean_object* l_Std_Http_instReprMethod_repr(uint8_t, lean_object*);
lean_object* l_Std_Http_instReprVersion_repr(uint8_t, lean_object*);
lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object*, lean_object*);
lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2(lean_object*);
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__3___closed__0 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__3___closed__0_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__3___closed__1 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__3___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__18 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__18_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__19 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__19_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__20 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__20_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__21 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__21_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__22 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__22_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__23 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__23_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "//"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__24 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__24_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__25 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__25_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__26 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__26_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ACL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__27 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__27_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BASELINE-CONTROL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__28 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__28_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "BIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__29 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__29_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CHECKIN"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__30 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__30_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CHECKOUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__31 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__31_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CONNECT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__32 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__32_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COPY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__33 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__33_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DELETE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__34 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__34_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__35 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__35_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__36 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__36_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "LABEL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__37 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__37_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LINK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__38 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__38_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LOCK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__39 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__39_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MERGE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__40 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__40_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKACTIVITY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__41 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__41_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKCALENDAR"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__42 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__42_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MKCOL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__43 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__43_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MKREDIRECTREF"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__44 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__44_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MKWORKSPACE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__45 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__45_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MOVE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__46 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__46_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__47 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__47_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ORDERPATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__48 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__48_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__49 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__49_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__50 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__50_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRI"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__51 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__51_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PROPFIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__52 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__52_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PROPPATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__53 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__53_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__54 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__54_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "QUERY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__55 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__55_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REBIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__56 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__56_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REPORT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__57 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__57_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SEARCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__58 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__58_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TRACE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__59 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__59_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNBIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__60 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__60_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UNCHECKOUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__61 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__61_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLINK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__62 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__62_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLOCK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__63 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__63_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UPDATE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__64 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__64_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UPDATEREDIRECTREF"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__65 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__65_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__6___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "VERSION-CONTROL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__6___closed__66 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__6___closed__66_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__0 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__1 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__1_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__2 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__2_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___closed__2_value)} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__3 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__3_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__6, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___closed__3_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__1_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__1_value)} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__4 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__4_value;
LEAN_EXPORT const lean_object* l_Std_Http_Request_instToStringHead = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___closed__1;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Request_instEncodeV11Head___lam__2___closed__2;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2___closed__4;
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Request_instEncodeV11Head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instEncodeV11Head___lam__3___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___closed__2_value)} };
static const lean_object* l_Std_Http_Request_instEncodeV11Head___closed__0 = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__0_value;
static const lean_closure_object l_Std_Http_Request_instEncodeV11Head___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instEncodeV11Head___lam__2, .m_arity = 7, .m_num_fixed = 5, .m_objs = {((lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__0_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__1_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value),((lean_object*)&l_Std_Http_Request_instToStringHead___closed__1_value)} };
static const lean_object* l_Std_Http_Request_instEncodeV11Head___closed__1 = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Request_instEncodeV11Head = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__1_value;
static lean_once_cell_t l_Std_Http_Request_new___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_new___closed__0;
static lean_once_cell_t l_Std_Http_Request_new___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_new___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_Request_new;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_empty;
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
static const lean_string_object l_Std_Http_Request_Builder_uri_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Std.Internal.Http.Data.URI"};
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
v___x_1_ = l_Std_Http_instInhabitedHeaders_default;
v___x_2_ = l_Std_Http_instInhabitedRequestTarget_default;
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
v___x_112_ = l_Std_Http_instInhabitedExtensions_default;
v___x_113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set(v___x_113_, 1, v_inst_110_);
lean_ctor_set(v___x_113_, 2, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest_default(lean_object* v_a_114_, lean_object* v_inst_115_){
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
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2(lean_object* v_x_128_){
_start:
{
lean_object* v___x_129_; uint32_t v___x_130_; uint32_t v___x_131_; uint8_t v___x_132_; 
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_string_utf8_get(v_x_128_, v___x_129_);
v___x_131_ = 97;
v___x_132_ = lean_uint32_dec_le(v___x_131_, v___x_130_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
v___x_133_ = lean_string_utf8_set(v_x_128_, v___x_129_, v___x_130_);
return v___x_133_;
}
else
{
uint32_t v___x_134_; uint8_t v___x_135_; 
v___x_134_ = 122;
v___x_135_ = lean_uint32_dec_le(v___x_130_, v___x_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
v___x_136_ = lean_string_utf8_set(v_x_128_, v___x_129_, v___x_130_);
return v___x_136_;
}
else
{
uint32_t v___x_137_; uint32_t v___x_138_; lean_object* v___x_139_; 
v___x_137_ = 4294967264;
v___x_138_ = lean_uint32_add(v___x_130_, v___x_137_);
v___x_139_ = lean_string_utf8_set(v_x_128_, v___x_129_, v___x_138_);
return v___x_139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__3(lean_object* v___f_142_, lean_object* v_x_143_){
_start:
{
lean_object* v_fst_144_; lean_object* v_snd_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v_it_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_fst_144_ = lean_ctor_get(v_x_143_, 0);
v_snd_145_ = lean_ctor_get(v_x_143_, 1);
v___x_146_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__0));
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_box(0);
v___x_149_ = l_String_splitOnAux(v_fst_144_, v___x_146_, v___x_147_, v___x_147_, v___x_147_, v___x_148_);
v_it_150_ = l_List_mapTR_loop___redArg(v___f_142_, v___x_149_, v___x_148_);
v___x_151_ = l_String_intercalate(v___x_146_, v_it_150_);
v___x_152_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__1));
v___x_153_ = lean_string_append(v___x_151_, v___x_152_);
v___x_154_ = lean_string_append(v___x_153_, v_snd_145_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__3___boxed(lean_object* v___f_155_, lean_object* v_x_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_Http_Request_instToStringHead___lam__3(v___f_155_, v_x_156_);
lean_dec_ref(v_x_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__6(lean_object* v___f_234_, lean_object* v___f_235_, lean_object* v___f_236_, lean_object* v___f_237_, lean_object* v___f_238_, lean_object* v_req_239_){
_start:
{
uint8_t v_method_240_; uint8_t v_version_241_; lean_object* v_uri_242_; lean_object* v_headers_243_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v_port_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v_host_390_; lean_object* v_port_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v_port_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_425_; lean_object* v_host_426_; lean_object* v_port_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_440_; 
v_method_240_ = lean_ctor_get_uint8(v_req_239_, sizeof(void*)*2);
v_version_241_ = lean_ctor_get_uint8(v_req_239_, sizeof(void*)*2 + 1);
v_uri_242_ = lean_ctor_get(v_req_239_, 0);
lean_inc(v_uri_242_);
v_headers_243_ = lean_ctor_get(v_req_239_, 1);
lean_inc_ref(v_headers_243_);
lean_dec_ref(v_req_239_);
switch(v_method_240_)
{
case 0:
{
lean_object* v___x_512_; 
v___x_512_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__27));
v___y_440_ = v___x_512_;
goto v___jp_439_;
}
case 1:
{
lean_object* v___x_513_; 
v___x_513_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__28));
v___y_440_ = v___x_513_;
goto v___jp_439_;
}
case 2:
{
lean_object* v___x_514_; 
v___x_514_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__29));
v___y_440_ = v___x_514_;
goto v___jp_439_;
}
case 3:
{
lean_object* v___x_515_; 
v___x_515_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__30));
v___y_440_ = v___x_515_;
goto v___jp_439_;
}
case 4:
{
lean_object* v___x_516_; 
v___x_516_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__31));
v___y_440_ = v___x_516_;
goto v___jp_439_;
}
case 5:
{
lean_object* v___x_517_; 
v___x_517_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__32));
v___y_440_ = v___x_517_;
goto v___jp_439_;
}
case 6:
{
lean_object* v___x_518_; 
v___x_518_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__33));
v___y_440_ = v___x_518_;
goto v___jp_439_;
}
case 7:
{
lean_object* v___x_519_; 
v___x_519_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__34));
v___y_440_ = v___x_519_;
goto v___jp_439_;
}
case 8:
{
lean_object* v___x_520_; 
v___x_520_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__35));
v___y_440_ = v___x_520_;
goto v___jp_439_;
}
case 9:
{
lean_object* v___x_521_; 
v___x_521_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__36));
v___y_440_ = v___x_521_;
goto v___jp_439_;
}
case 10:
{
lean_object* v___x_522_; 
v___x_522_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__37));
v___y_440_ = v___x_522_;
goto v___jp_439_;
}
case 11:
{
lean_object* v___x_523_; 
v___x_523_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__38));
v___y_440_ = v___x_523_;
goto v___jp_439_;
}
case 12:
{
lean_object* v___x_524_; 
v___x_524_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__39));
v___y_440_ = v___x_524_;
goto v___jp_439_;
}
case 13:
{
lean_object* v___x_525_; 
v___x_525_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__40));
v___y_440_ = v___x_525_;
goto v___jp_439_;
}
case 14:
{
lean_object* v___x_526_; 
v___x_526_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__41));
v___y_440_ = v___x_526_;
goto v___jp_439_;
}
case 15:
{
lean_object* v___x_527_; 
v___x_527_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__42));
v___y_440_ = v___x_527_;
goto v___jp_439_;
}
case 16:
{
lean_object* v___x_528_; 
v___x_528_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__43));
v___y_440_ = v___x_528_;
goto v___jp_439_;
}
case 17:
{
lean_object* v___x_529_; 
v___x_529_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__44));
v___y_440_ = v___x_529_;
goto v___jp_439_;
}
case 18:
{
lean_object* v___x_530_; 
v___x_530_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__45));
v___y_440_ = v___x_530_;
goto v___jp_439_;
}
case 19:
{
lean_object* v___x_531_; 
v___x_531_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__46));
v___y_440_ = v___x_531_;
goto v___jp_439_;
}
case 20:
{
lean_object* v___x_532_; 
v___x_532_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__47));
v___y_440_ = v___x_532_;
goto v___jp_439_;
}
case 21:
{
lean_object* v___x_533_; 
v___x_533_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__48));
v___y_440_ = v___x_533_;
goto v___jp_439_;
}
case 22:
{
lean_object* v___x_534_; 
v___x_534_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__49));
v___y_440_ = v___x_534_;
goto v___jp_439_;
}
case 23:
{
lean_object* v___x_535_; 
v___x_535_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__50));
v___y_440_ = v___x_535_;
goto v___jp_439_;
}
case 24:
{
lean_object* v___x_536_; 
v___x_536_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__51));
v___y_440_ = v___x_536_;
goto v___jp_439_;
}
case 25:
{
lean_object* v___x_537_; 
v___x_537_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__52));
v___y_440_ = v___x_537_;
goto v___jp_439_;
}
case 26:
{
lean_object* v___x_538_; 
v___x_538_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__53));
v___y_440_ = v___x_538_;
goto v___jp_439_;
}
case 27:
{
lean_object* v___x_539_; 
v___x_539_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__54));
v___y_440_ = v___x_539_;
goto v___jp_439_;
}
case 28:
{
lean_object* v___x_540_; 
v___x_540_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__55));
v___y_440_ = v___x_540_;
goto v___jp_439_;
}
case 29:
{
lean_object* v___x_541_; 
v___x_541_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__56));
v___y_440_ = v___x_541_;
goto v___jp_439_;
}
case 30:
{
lean_object* v___x_542_; 
v___x_542_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__57));
v___y_440_ = v___x_542_;
goto v___jp_439_;
}
case 31:
{
lean_object* v___x_543_; 
v___x_543_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__58));
v___y_440_ = v___x_543_;
goto v___jp_439_;
}
case 32:
{
lean_object* v___x_544_; 
v___x_544_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__59));
v___y_440_ = v___x_544_;
goto v___jp_439_;
}
case 33:
{
lean_object* v___x_545_; 
v___x_545_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__60));
v___y_440_ = v___x_545_;
goto v___jp_439_;
}
case 34:
{
lean_object* v___x_546_; 
v___x_546_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__61));
v___y_440_ = v___x_546_;
goto v___jp_439_;
}
case 35:
{
lean_object* v___x_547_; 
v___x_547_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__62));
v___y_440_ = v___x_547_;
goto v___jp_439_;
}
case 36:
{
lean_object* v___x_548_; 
v___x_548_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__63));
v___y_440_ = v___x_548_;
goto v___jp_439_;
}
case 37:
{
lean_object* v___x_549_; 
v___x_549_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__64));
v___y_440_ = v___x_549_;
goto v___jp_439_;
}
case 38:
{
lean_object* v___x_550_; 
v___x_550_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__65));
v___y_440_ = v___x_550_;
goto v___jp_439_;
}
default: 
{
lean_object* v___x_551_; 
v___x_551_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__66));
v___y_440_ = v___x_551_;
goto v___jp_439_;
}
}
v___jp_244_:
{
lean_object* v_entries_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; size_t v_sz_252_; size_t v___x_253_; lean_object* v_pairs_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_entries_247_ = lean_ctor_get(v_headers_243_, 0);
lean_inc_ref(v_entries_247_);
lean_dec_ref(v_headers_243_);
v___x_248_ = lean_string_append(v___y_245_, v___y_246_);
v___x_249_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__0));
v___x_250_ = lean_string_append(v___x_248_, v___x_249_);
v___x_251_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__10));
v_sz_252_ = lean_array_size(v_entries_247_);
v___x_253_ = ((size_t)0ULL);
v_pairs_254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_251_, v___f_234_, v_sz_252_, v___x_253_, v_entries_247_);
v___x_255_ = lean_array_to_list(v_pairs_254_);
v___x_256_ = l_String_intercalate(v___x_249_, v___x_255_);
v___x_257_ = lean_string_append(v___x_250_, v___x_256_);
lean_dec_ref(v___x_256_);
v___x_258_ = lean_string_append(v___x_257_, v___x_249_);
return v___x_258_;
}
v___jp_259_:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_string_append(v___y_261_, v___y_262_);
lean_dec_ref(v___y_262_);
v___x_264_ = lean_string_append(v___x_263_, v___y_260_);
switch(v_version_241_)
{
case 0:
{
lean_object* v___x_265_; 
v___x_265_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__11));
v___y_245_ = v___x_264_;
v___y_246_ = v___x_265_;
goto v___jp_244_;
}
case 1:
{
lean_object* v___x_266_; 
v___x_266_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__12));
v___y_245_ = v___x_264_;
v___y_246_ = v___x_266_;
goto v___jp_244_;
}
case 2:
{
lean_object* v___x_267_; 
v___x_267_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__13));
v___y_245_ = v___x_264_;
v___y_246_ = v___x_267_;
goto v___jp_244_;
}
default: 
{
lean_object* v___x_268_; 
v___x_268_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__14));
v___y_245_ = v___x_264_;
v___y_246_ = v___x_268_;
goto v___jp_244_;
}
}
}
v___jp_269_:
{
if (lean_obj_tag(v___y_272_) == 0)
{
lean_dec_ref(v___f_235_);
v___y_260_ = v___y_270_;
v___y_261_ = v___y_271_;
v___y_262_ = v___y_273_;
goto v___jp_259_;
}
else
{
lean_object* v_val_274_; lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v_val_274_ = lean_ctor_get(v___y_272_, 0);
lean_inc(v_val_274_);
lean_dec_ref(v___y_272_);
v___x_275_ = lean_array_get_size(v_val_274_);
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_nat_dec_eq(v___x_275_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v_encodedParams_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_278_ = lean_array_to_list(v_val_274_);
v___x_279_ = lean_box(0);
v_encodedParams_280_ = l_List_mapTR_loop___redArg(v___f_235_, v___x_278_, v___x_279_);
v___x_281_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__15));
v___x_282_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__16));
v___x_283_ = l_String_intercalate(v___x_282_, v_encodedParams_280_);
v___x_284_ = lean_string_append(v___x_281_, v___x_283_);
lean_dec_ref(v___x_283_);
v___x_285_ = lean_string_append(v___y_273_, v___x_284_);
lean_dec_ref(v___x_284_);
v___y_260_ = v___y_270_;
v___y_261_ = v___y_271_;
v___y_262_ = v___x_285_;
goto v___jp_259_;
}
else
{
lean_dec(v_val_274_);
lean_dec_ref(v___f_235_);
v___y_260_ = v___y_270_;
v___y_261_ = v___y_271_;
v___y_262_ = v___y_273_;
goto v___jp_259_;
}
}
}
v___jp_286_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_294_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_295_ = lean_string_append(v___y_292_, v___x_294_);
v___x_296_ = lean_string_append(v___x_295_, v___y_291_);
lean_dec_ref(v___y_291_);
v___x_297_ = lean_string_append(v___x_296_, v___y_289_);
lean_dec_ref(v___y_289_);
v___x_298_ = lean_string_append(v___x_297_, v___y_288_);
lean_dec_ref(v___y_288_);
v___x_299_ = lean_string_append(v___x_298_, v___y_293_);
lean_dec_ref(v___y_293_);
v___y_260_ = v___y_287_;
v___y_261_ = v___y_290_;
v___y_262_ = v___x_299_;
goto v___jp_259_;
}
v___jp_300_:
{
if (lean_obj_tag(v___y_302_) == 0)
{
lean_object* v___x_308_; 
v___x_308_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__18));
v___y_287_ = v___y_301_;
v___y_288_ = v___y_307_;
v___y_289_ = v___y_303_;
v___y_290_ = v___y_305_;
v___y_291_ = v___y_304_;
v___y_292_ = v___y_306_;
v___y_293_ = v___x_308_;
goto v___jp_286_;
}
else
{
lean_object* v_val_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_val_309_ = lean_ctor_get(v___y_302_, 0);
lean_inc(v_val_309_);
lean_dec_ref(v___y_302_);
v___x_310_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__19));
v___x_311_ = l_Std_Http_URI_EncodedFragment_encode(v_val_309_);
lean_dec(v_val_309_);
v___x_312_ = lean_string_from_utf8_unchecked(v___x_311_);
v___x_313_ = lean_string_append(v___x_310_, v___x_312_);
lean_dec_ref(v___x_312_);
v___y_287_ = v___y_301_;
v___y_288_ = v___y_307_;
v___y_289_ = v___y_303_;
v___y_290_ = v___y_305_;
v___y_291_ = v___y_304_;
v___y_292_ = v___y_306_;
v___y_293_ = v___x_313_;
goto v___jp_286_;
}
}
v___jp_314_:
{
lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_322_ = lean_array_get_size(v___y_317_);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_nat_dec_eq(v___x_322_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v_encodedParams_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_325_ = lean_array_to_list(v___y_317_);
v___x_326_ = lean_box(0);
v_encodedParams_327_ = l_List_mapTR_loop___redArg(v___f_236_, v___x_325_, v___x_326_);
v___x_328_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__15));
v___x_329_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__16));
v___x_330_ = l_String_intercalate(v___x_329_, v_encodedParams_327_);
v___x_331_ = lean_string_append(v___x_328_, v___x_330_);
lean_dec_ref(v___x_330_);
v___y_301_ = v___y_315_;
v___y_302_ = v___y_316_;
v___y_303_ = v___y_321_;
v___y_304_ = v___y_319_;
v___y_305_ = v___y_318_;
v___y_306_ = v___y_320_;
v___y_307_ = v___x_331_;
goto v___jp_300_;
}
else
{
lean_object* v___x_332_; 
lean_dec_ref(v___y_317_);
lean_dec_ref(v___f_236_);
v___x_332_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__18));
v___y_301_ = v___y_315_;
v___y_302_ = v___y_316_;
v___y_303_ = v___y_321_;
v___y_304_ = v___y_319_;
v___y_305_ = v___y_318_;
v___y_306_ = v___y_320_;
v___y_307_ = v___x_332_;
goto v___jp_300_;
}
}
v___jp_333_:
{
lean_object* v_segments_341_; uint8_t v_absolute_342_; lean_object* v___x_343_; lean_object* v___x_344_; size_t v_sz_345_; size_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v_result_349_; 
v_segments_341_ = lean_ctor_get(v___y_334_, 0);
lean_inc_ref(v_segments_341_);
v_absolute_342_ = lean_ctor_get_uint8(v___y_334_, sizeof(void*)*1);
lean_dec_ref(v___y_334_);
v___x_343_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__20));
v___x_344_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__10));
v_sz_345_ = lean_array_size(v_segments_341_);
v___x_346_ = ((size_t)0ULL);
v___x_347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_344_, v___f_237_, v_sz_345_, v___x_346_, v_segments_341_);
v___x_348_ = lean_array_to_list(v___x_347_);
v_result_349_ = l_String_intercalate(v___x_343_, v___x_348_);
if (v_absolute_342_ == 0)
{
v___y_315_ = v___y_335_;
v___y_316_ = v___y_336_;
v___y_317_ = v___y_337_;
v___y_318_ = v___y_338_;
v___y_319_ = v___y_340_;
v___y_320_ = v___y_339_;
v___y_321_ = v_result_349_;
goto v___jp_314_;
}
else
{
lean_object* v___x_350_; 
v___x_350_ = lean_string_append(v___x_343_, v_result_349_);
lean_dec_ref(v_result_349_);
v___y_315_ = v___y_335_;
v___y_316_ = v___y_336_;
v___y_317_ = v___y_337_;
v___y_318_ = v___y_338_;
v___y_319_ = v___y_340_;
v___y_320_ = v___y_339_;
v___y_321_ = v___x_350_;
goto v___jp_314_;
}
}
v___jp_351_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_string_append(v___y_357_, v___y_359_);
lean_dec_ref(v___y_359_);
v___x_363_ = lean_string_append(v___x_362_, v___y_361_);
lean_dec_ref(v___y_361_);
lean_inc_ref(v___y_356_);
v___x_364_ = lean_string_append(v___y_356_, v___x_363_);
lean_dec_ref(v___x_363_);
v___y_334_ = v___y_353_;
v___y_335_ = v___y_352_;
v___y_336_ = v___y_354_;
v___y_337_ = v___y_355_;
v___y_338_ = v___y_358_;
v___y_339_ = v___y_360_;
v___y_340_ = v___x_364_;
goto v___jp_333_;
}
v___jp_365_:
{
switch(lean_obj_tag(v_port_373_))
{
case 0:
{
lean_object* v___x_376_; 
v___x_376_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__18));
v___y_352_ = v___y_367_;
v___y_353_ = v___y_366_;
v___y_354_ = v___y_368_;
v___y_355_ = v___y_369_;
v___y_356_ = v___y_371_;
v___y_357_ = v___y_370_;
v___y_358_ = v___y_372_;
v___y_359_ = v___y_375_;
v___y_360_ = v___y_374_;
v___y_361_ = v___x_376_;
goto v___jp_351_;
}
case 1:
{
lean_object* v___x_377_; 
v___x_377_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___y_352_ = v___y_367_;
v___y_353_ = v___y_366_;
v___y_354_ = v___y_368_;
v___y_355_ = v___y_369_;
v___y_356_ = v___y_371_;
v___y_357_ = v___y_370_;
v___y_358_ = v___y_372_;
v___y_359_ = v___y_375_;
v___y_360_ = v___y_374_;
v___y_361_ = v___x_377_;
goto v___jp_351_;
}
default: 
{
uint16_t v_port_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v_port_378_ = lean_ctor_get_uint16(v_port_373_, 0);
lean_dec_ref(v_port_373_);
v___x_379_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_380_ = lean_uint16_to_nat(v_port_378_);
v___x_381_ = l_Nat_reprFast(v___x_380_);
v___x_382_ = lean_string_append(v___x_379_, v___x_381_);
lean_dec_ref(v___x_381_);
v___y_352_ = v___y_367_;
v___y_353_ = v___y_366_;
v___y_354_ = v___y_368_;
v___y_355_ = v___y_369_;
v___y_356_ = v___y_371_;
v___y_357_ = v___y_370_;
v___y_358_ = v___y_372_;
v___y_359_ = v___y_375_;
v___y_360_ = v___y_374_;
v___y_361_ = v___x_382_;
goto v___jp_351_;
}
}
}
v___jp_383_:
{
switch(lean_obj_tag(v_host_390_))
{
case 0:
{
lean_object* v_name_394_; 
v_name_394_ = lean_ctor_get(v_host_390_, 0);
lean_inc_ref(v_name_394_);
lean_dec_ref(v_host_390_);
v___y_366_ = v___y_385_;
v___y_367_ = v___y_384_;
v___y_368_ = v___y_386_;
v___y_369_ = v___y_387_;
v___y_370_ = v___y_393_;
v___y_371_ = v___y_388_;
v___y_372_ = v___y_389_;
v_port_373_ = v_port_391_;
v___y_374_ = v___y_392_;
v___y_375_ = v_name_394_;
goto v___jp_365_;
}
case 1:
{
lean_object* v_ipv4_395_; lean_object* v___x_396_; 
v_ipv4_395_ = lean_ctor_get(v_host_390_, 0);
lean_inc_ref(v_ipv4_395_);
lean_dec_ref(v_host_390_);
v___x_396_ = lean_uv_ntop_v4(v_ipv4_395_);
lean_dec_ref(v_ipv4_395_);
v___y_366_ = v___y_385_;
v___y_367_ = v___y_384_;
v___y_368_ = v___y_386_;
v___y_369_ = v___y_387_;
v___y_370_ = v___y_393_;
v___y_371_ = v___y_388_;
v___y_372_ = v___y_389_;
v_port_373_ = v_port_391_;
v___y_374_ = v___y_392_;
v___y_375_ = v___x_396_;
goto v___jp_365_;
}
default: 
{
lean_object* v_ipv6_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_ipv6_397_ = lean_ctor_get(v_host_390_, 0);
lean_inc_ref(v_ipv6_397_);
lean_dec_ref(v_host_390_);
v___x_398_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__21));
v___x_399_ = lean_uv_ntop_v6(v_ipv6_397_);
lean_dec_ref(v_ipv6_397_);
v___x_400_ = lean_string_append(v___x_398_, v___x_399_);
lean_dec_ref(v___x_399_);
v___x_401_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__22));
v___x_402_ = lean_string_append(v___x_400_, v___x_401_);
v___y_366_ = v___y_385_;
v___y_367_ = v___y_384_;
v___y_368_ = v___y_386_;
v___y_369_ = v___y_387_;
v___y_370_ = v___y_393_;
v___y_371_ = v___y_388_;
v___y_372_ = v___y_389_;
v_port_373_ = v_port_391_;
v___y_374_ = v___y_392_;
v___y_375_ = v___x_402_;
goto v___jp_365_;
}
}
}
v___jp_403_:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_string_append(v___y_405_, v___y_406_);
lean_dec_ref(v___y_406_);
v___x_410_ = lean_string_append(v___x_409_, v___y_408_);
lean_dec_ref(v___y_408_);
v___y_260_ = v___y_404_;
v___y_261_ = v___y_407_;
v___y_262_ = v___x_410_;
goto v___jp_259_;
}
v___jp_411_:
{
switch(lean_obj_tag(v_port_414_))
{
case 0:
{
lean_object* v___x_417_; 
v___x_417_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__18));
v___y_404_ = v___y_412_;
v___y_405_ = v___y_413_;
v___y_406_ = v___y_416_;
v___y_407_ = v___y_415_;
v___y_408_ = v___x_417_;
goto v___jp_403_;
}
case 1:
{
lean_object* v___x_418_; 
v___x_418_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___y_404_ = v___y_412_;
v___y_405_ = v___y_413_;
v___y_406_ = v___y_416_;
v___y_407_ = v___y_415_;
v___y_408_ = v___x_418_;
goto v___jp_403_;
}
default: 
{
uint16_t v_port_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_port_419_ = lean_ctor_get_uint16(v_port_414_, 0);
lean_dec_ref(v_port_414_);
v___x_420_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_421_ = lean_uint16_to_nat(v_port_419_);
v___x_422_ = l_Nat_reprFast(v___x_421_);
v___x_423_ = lean_string_append(v___x_420_, v___x_422_);
lean_dec_ref(v___x_422_);
v___y_404_ = v___y_412_;
v___y_405_ = v___y_413_;
v___y_406_ = v___y_416_;
v___y_407_ = v___y_415_;
v___y_408_ = v___x_423_;
goto v___jp_403_;
}
}
}
v___jp_424_:
{
switch(lean_obj_tag(v_host_426_))
{
case 0:
{
lean_object* v_name_430_; 
v_name_430_ = lean_ctor_get(v_host_426_, 0);
lean_inc_ref(v_name_430_);
lean_dec_ref(v_host_426_);
v___y_412_ = v___y_425_;
v___y_413_ = v___y_429_;
v_port_414_ = v_port_427_;
v___y_415_ = v___y_428_;
v___y_416_ = v_name_430_;
goto v___jp_411_;
}
case 1:
{
lean_object* v_ipv4_431_; lean_object* v___x_432_; 
v_ipv4_431_ = lean_ctor_get(v_host_426_, 0);
lean_inc_ref(v_ipv4_431_);
lean_dec_ref(v_host_426_);
v___x_432_ = lean_uv_ntop_v4(v_ipv4_431_);
lean_dec_ref(v_ipv4_431_);
v___y_412_ = v___y_425_;
v___y_413_ = v___y_429_;
v_port_414_ = v_port_427_;
v___y_415_ = v___y_428_;
v___y_416_ = v___x_432_;
goto v___jp_411_;
}
default: 
{
lean_object* v_ipv6_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_ipv6_433_ = lean_ctor_get(v_host_426_, 0);
lean_inc_ref(v_ipv6_433_);
lean_dec_ref(v_host_426_);
v___x_434_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__21));
v___x_435_ = lean_uv_ntop_v6(v_ipv6_433_);
lean_dec_ref(v_ipv6_433_);
v___x_436_ = lean_string_append(v___x_434_, v___x_435_);
lean_dec_ref(v___x_435_);
v___x_437_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__22));
v___x_438_ = lean_string_append(v___x_436_, v___x_437_);
v___y_412_ = v___y_425_;
v___y_413_ = v___y_429_;
v_port_414_ = v_port_427_;
v___y_415_ = v___y_428_;
v___y_416_ = v___x_438_;
goto v___jp_411_;
}
}
}
v___jp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__23));
lean_inc_ref(v___y_440_);
v___x_442_ = lean_string_append(v___y_440_, v___x_441_);
switch(lean_obj_tag(v_uri_242_))
{
case 0:
{
lean_object* v_path_443_; lean_object* v_query_444_; lean_object* v_segments_445_; uint8_t v_absolute_446_; lean_object* v___x_447_; lean_object* v___x_448_; size_t v_sz_449_; size_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v_result_453_; 
lean_dec_ref(v___f_237_);
lean_dec_ref(v___f_236_);
v_path_443_ = lean_ctor_get(v_uri_242_, 0);
lean_inc_ref(v_path_443_);
v_query_444_ = lean_ctor_get(v_uri_242_, 1);
lean_inc(v_query_444_);
lean_dec_ref(v_uri_242_);
v_segments_445_ = lean_ctor_get(v_path_443_, 0);
lean_inc_ref(v_segments_445_);
v_absolute_446_ = lean_ctor_get_uint8(v_path_443_, sizeof(void*)*1);
lean_dec_ref(v_path_443_);
v___x_447_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__20));
v___x_448_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__10));
v_sz_449_ = lean_array_size(v_segments_445_);
v___x_450_ = ((size_t)0ULL);
v___x_451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_448_, v___f_238_, v_sz_449_, v___x_450_, v_segments_445_);
v___x_452_ = lean_array_to_list(v___x_451_);
v_result_453_ = l_String_intercalate(v___x_447_, v___x_452_);
if (v_absolute_446_ == 0)
{
v___y_270_ = v___x_441_;
v___y_271_ = v___x_442_;
v___y_272_ = v_query_444_;
v___y_273_ = v_result_453_;
goto v___jp_269_;
}
else
{
lean_object* v___x_454_; 
v___x_454_ = lean_string_append(v___x_447_, v_result_453_);
lean_dec_ref(v_result_453_);
v___y_270_ = v___x_441_;
v___y_271_ = v___x_442_;
v___y_272_ = v_query_444_;
v___y_273_ = v___x_454_;
goto v___jp_269_;
}
}
case 1:
{
lean_object* v_uri_455_; lean_object* v_authority_456_; 
lean_dec_ref(v___f_238_);
lean_dec_ref(v___f_235_);
v_uri_455_ = lean_ctor_get(v_uri_242_, 0);
lean_inc_ref(v_uri_455_);
lean_dec_ref(v_uri_242_);
v_authority_456_ = lean_ctor_get(v_uri_455_, 1);
if (lean_obj_tag(v_authority_456_) == 0)
{
lean_object* v_scheme_457_; lean_object* v_path_458_; lean_object* v_query_459_; lean_object* v_fragment_460_; lean_object* v___x_461_; 
v_scheme_457_ = lean_ctor_get(v_uri_455_, 0);
lean_inc_ref(v_scheme_457_);
v_path_458_ = lean_ctor_get(v_uri_455_, 2);
lean_inc_ref(v_path_458_);
v_query_459_ = lean_ctor_get(v_uri_455_, 3);
lean_inc_ref(v_query_459_);
v_fragment_460_ = lean_ctor_get(v_uri_455_, 4);
lean_inc(v_fragment_460_);
lean_dec_ref(v_uri_455_);
v___x_461_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__18));
v___y_334_ = v_path_458_;
v___y_335_ = v___x_441_;
v___y_336_ = v_fragment_460_;
v___y_337_ = v_query_459_;
v___y_338_ = v___x_442_;
v___y_339_ = v_scheme_457_;
v___y_340_ = v___x_461_;
goto v___jp_333_;
}
else
{
lean_object* v_val_462_; lean_object* v_scheme_463_; lean_object* v_path_464_; lean_object* v_query_465_; lean_object* v_fragment_466_; lean_object* v_userInfo_467_; lean_object* v_host_468_; lean_object* v_port_469_; lean_object* v___x_470_; 
v_val_462_ = lean_ctor_get(v_authority_456_, 0);
lean_inc(v_val_462_);
v_scheme_463_ = lean_ctor_get(v_uri_455_, 0);
lean_inc_ref(v_scheme_463_);
v_path_464_ = lean_ctor_get(v_uri_455_, 2);
lean_inc_ref(v_path_464_);
v_query_465_ = lean_ctor_get(v_uri_455_, 3);
lean_inc_ref(v_query_465_);
v_fragment_466_ = lean_ctor_get(v_uri_455_, 4);
lean_inc(v_fragment_466_);
lean_dec_ref(v_uri_455_);
v_userInfo_467_ = lean_ctor_get(v_val_462_, 0);
lean_inc(v_userInfo_467_);
v_host_468_ = lean_ctor_get(v_val_462_, 1);
lean_inc_ref(v_host_468_);
v_port_469_ = lean_ctor_get(v_val_462_, 2);
lean_inc(v_port_469_);
lean_dec(v_val_462_);
v___x_470_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__24));
if (lean_obj_tag(v_userInfo_467_) == 0)
{
lean_object* v___x_471_; 
v___x_471_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__18));
v___y_384_ = v___x_441_;
v___y_385_ = v_path_464_;
v___y_386_ = v_fragment_466_;
v___y_387_ = v_query_465_;
v___y_388_ = v___x_470_;
v___y_389_ = v___x_442_;
v_host_390_ = v_host_468_;
v_port_391_ = v_port_469_;
v___y_392_ = v_scheme_463_;
v___y_393_ = v___x_471_;
goto v___jp_383_;
}
else
{
lean_object* v_val_472_; lean_object* v_password_473_; 
v_val_472_ = lean_ctor_get(v_userInfo_467_, 0);
lean_inc(v_val_472_);
lean_dec_ref(v_userInfo_467_);
v_password_473_ = lean_ctor_get(v_val_472_, 1);
if (lean_obj_tag(v_password_473_) == 0)
{
lean_object* v_username_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_username_474_ = lean_ctor_get(v_val_472_, 0);
lean_inc_ref(v_username_474_);
lean_dec(v_val_472_);
v___x_475_ = lean_string_from_utf8_unchecked(v_username_474_);
v___x_476_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__25));
v___x_477_ = lean_string_append(v___x_475_, v___x_476_);
v___y_384_ = v___x_441_;
v___y_385_ = v_path_464_;
v___y_386_ = v_fragment_466_;
v___y_387_ = v_query_465_;
v___y_388_ = v___x_470_;
v___y_389_ = v___x_442_;
v_host_390_ = v_host_468_;
v_port_391_ = v_port_469_;
v___y_392_ = v_scheme_463_;
v___y_393_ = v___x_477_;
goto v___jp_383_;
}
else
{
lean_object* v_username_478_; lean_object* v_val_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
lean_inc_ref(v_password_473_);
v_username_478_ = lean_ctor_get(v_val_472_, 0);
lean_inc_ref(v_username_478_);
lean_dec(v_val_472_);
v_val_479_ = lean_ctor_get(v_password_473_, 0);
lean_inc(v_val_479_);
lean_dec_ref(v_password_473_);
v___x_480_ = lean_string_from_utf8_unchecked(v_username_478_);
v___x_481_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_482_ = lean_string_append(v___x_480_, v___x_481_);
v___x_483_ = lean_string_from_utf8_unchecked(v_val_479_);
v___x_484_ = lean_string_append(v___x_482_, v___x_483_);
lean_dec_ref(v___x_483_);
v___x_485_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__25));
v___x_486_ = lean_string_append(v___x_484_, v___x_485_);
v___y_384_ = v___x_441_;
v___y_385_ = v_path_464_;
v___y_386_ = v_fragment_466_;
v___y_387_ = v_query_465_;
v___y_388_ = v___x_470_;
v___y_389_ = v___x_442_;
v_host_390_ = v_host_468_;
v_port_391_ = v_port_469_;
v___y_392_ = v_scheme_463_;
v___y_393_ = v___x_486_;
goto v___jp_383_;
}
}
}
}
case 2:
{
lean_object* v_authority_487_; lean_object* v_userInfo_488_; 
lean_dec_ref(v___f_238_);
lean_dec_ref(v___f_237_);
lean_dec_ref(v___f_236_);
lean_dec_ref(v___f_235_);
v_authority_487_ = lean_ctor_get(v_uri_242_, 0);
lean_inc_ref(v_authority_487_);
lean_dec_ref(v_uri_242_);
v_userInfo_488_ = lean_ctor_get(v_authority_487_, 0);
if (lean_obj_tag(v_userInfo_488_) == 0)
{
lean_object* v_host_489_; lean_object* v_port_490_; lean_object* v___x_491_; 
v_host_489_ = lean_ctor_get(v_authority_487_, 1);
lean_inc_ref(v_host_489_);
v_port_490_ = lean_ctor_get(v_authority_487_, 2);
lean_inc(v_port_490_);
lean_dec_ref(v_authority_487_);
v___x_491_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__18));
v___y_425_ = v___x_441_;
v_host_426_ = v_host_489_;
v_port_427_ = v_port_490_;
v___y_428_ = v___x_442_;
v___y_429_ = v___x_491_;
goto v___jp_424_;
}
else
{
lean_object* v_val_492_; lean_object* v_password_493_; 
v_val_492_ = lean_ctor_get(v_userInfo_488_, 0);
lean_inc(v_val_492_);
v_password_493_ = lean_ctor_get(v_val_492_, 1);
if (lean_obj_tag(v_password_493_) == 0)
{
lean_object* v_host_494_; lean_object* v_port_495_; lean_object* v_username_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_host_494_ = lean_ctor_get(v_authority_487_, 1);
lean_inc_ref(v_host_494_);
v_port_495_ = lean_ctor_get(v_authority_487_, 2);
lean_inc(v_port_495_);
lean_dec_ref(v_authority_487_);
v_username_496_ = lean_ctor_get(v_val_492_, 0);
lean_inc_ref(v_username_496_);
lean_dec(v_val_492_);
v___x_497_ = lean_string_from_utf8_unchecked(v_username_496_);
v___x_498_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__25));
v___x_499_ = lean_string_append(v___x_497_, v___x_498_);
v___y_425_ = v___x_441_;
v_host_426_ = v_host_494_;
v_port_427_ = v_port_495_;
v___y_428_ = v___x_442_;
v___y_429_ = v___x_499_;
goto v___jp_424_;
}
else
{
lean_object* v_host_500_; lean_object* v_port_501_; lean_object* v_username_502_; lean_object* v_val_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
lean_inc_ref(v_password_493_);
v_host_500_ = lean_ctor_get(v_authority_487_, 1);
lean_inc_ref(v_host_500_);
v_port_501_ = lean_ctor_get(v_authority_487_, 2);
lean_inc(v_port_501_);
lean_dec_ref(v_authority_487_);
v_username_502_ = lean_ctor_get(v_val_492_, 0);
lean_inc_ref(v_username_502_);
lean_dec(v_val_492_);
v_val_503_ = lean_ctor_get(v_password_493_, 0);
lean_inc(v_val_503_);
lean_dec_ref(v_password_493_);
v___x_504_ = lean_string_from_utf8_unchecked(v_username_502_);
v___x_505_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_506_ = lean_string_append(v___x_504_, v___x_505_);
v___x_507_ = lean_string_from_utf8_unchecked(v_val_503_);
v___x_508_ = lean_string_append(v___x_506_, v___x_507_);
lean_dec_ref(v___x_507_);
v___x_509_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__25));
v___x_510_ = lean_string_append(v___x_508_, v___x_509_);
v___y_425_ = v___x_441_;
v_host_426_ = v_host_500_;
v_port_427_ = v_port_501_;
v___y_428_ = v___x_442_;
v___y_429_ = v___x_510_;
goto v___jp_424_;
}
}
}
default: 
{
lean_object* v___x_511_; 
lean_dec_ref(v___f_238_);
lean_dec_ref(v___f_237_);
lean_dec_ref(v___f_236_);
lean_dec_ref(v___f_235_);
v___x_511_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__26));
v___y_260_ = v___x_441_;
v___y_261_ = v___x_442_;
v___y_262_ = v___x_511_;
goto v___jp_259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3(lean_object* v___f_562_, lean_object* v_buf_563_, lean_object* v_name_564_, lean_object* v_value_565_){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v_data_570_; lean_object* v_size_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_589_; 
v___x_566_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__0));
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_box(0);
v___x_569_ = l_String_splitOnAux(v_name_564_, v___x_566_, v___x_567_, v___x_567_, v___x_567_, v___x_568_);
v_data_570_ = lean_ctor_get(v_buf_563_, 0);
v_size_571_ = lean_ctor_get(v_buf_563_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_buf_563_);
if (v_isSharedCheck_589_ == 0)
{
v___x_573_ = v_buf_563_;
v_isShared_574_ = v_isSharedCheck_589_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_size_571_);
lean_inc(v_data_570_);
lean_dec(v_buf_563_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_589_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v_it_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v_it_575_ = l_List_mapTR_loop___redArg(v___f_562_, v___x_569_, v___x_568_);
v___x_576_ = l_String_intercalate(v___x_566_, v_it_575_);
v___x_577_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__3___closed__1));
v___x_578_ = lean_string_append(v___x_576_, v___x_577_);
v___x_579_ = lean_string_append(v___x_578_, v_value_565_);
v___x_580_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__0));
v___x_581_ = lean_string_append(v___x_579_, v___x_580_);
v___x_582_ = lean_string_to_utf8(v___x_581_);
lean_dec_ref(v___x_581_);
lean_inc_ref(v___x_582_);
v___x_583_ = lean_array_push(v_data_570_, v___x_582_);
v___x_584_ = lean_byte_array_size(v___x_582_);
lean_dec_ref(v___x_582_);
v___x_585_ = lean_nat_add(v_size_571_, v___x_584_);
lean_dec(v_size_571_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v___x_585_);
lean_ctor_set(v___x_573_, 0, v___x_583_);
v___x_587_ = v___x_573_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__3___boxed(lean_object* v___f_590_, lean_object* v_buf_591_, lean_object* v_name_592_, lean_object* v_value_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Std_Http_Request_instEncodeV11Head___lam__3(v___f_590_, v_buf_591_, v_name_592_, v_value_593_);
lean_dec_ref(v_value_593_);
lean_dec_ref(v_name_592_);
return v_res_594_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__0));
v___x_596_ = lean_string_to_utf8(v___x_595_);
return v___x_596_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__1(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0);
v___x_598_ = lean_byte_array_size(v___x_597_);
return v___x_598_;
}
}
static uint8_t _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__2(void){
_start:
{
uint32_t v___x_599_; uint8_t v___x_600_; 
v___x_599_ = 32;
v___x_600_ = lean_uint32_to_uint8(v___x_599_);
return v___x_600_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3(void){
_start:
{
uint8_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_601_ = lean_uint8_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__2, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__2_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__2);
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_mk_empty_array_with_capacity(v___x_602_);
v___x_604_ = lean_box(v___x_601_);
v___x_605_ = lean_array_push(v___x_603_, v___x_604_);
v___x_606_ = lean_byte_array_mk(v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__4(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3);
v___x_608_ = lean_byte_array_size(v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__2(lean_object* v___f_609_, lean_object* v___f_610_, lean_object* v___f_611_, lean_object* v___f_612_, lean_object* v___f_613_, lean_object* v_buffer_614_, lean_object* v_req_615_){
_start:
{
uint8_t v_method_616_; uint8_t v_version_617_; lean_object* v_uri_618_; lean_object* v_headers_619_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v_port_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_687_; lean_object* v_host_688_; lean_object* v_port_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v_port_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v_host_817_; lean_object* v_port_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_854_; 
v_method_616_ = lean_ctor_get_uint8(v_req_615_, sizeof(void*)*2);
v_version_617_ = lean_ctor_get_uint8(v_req_615_, sizeof(void*)*2 + 1);
v_uri_618_ = lean_ctor_get(v_req_615_, 0);
lean_inc(v_uri_618_);
v_headers_619_ = lean_ctor_get(v_req_615_, 1);
lean_inc_ref(v_headers_619_);
lean_dec_ref(v_req_615_);
switch(v_method_616_)
{
case 0:
{
lean_object* v___x_934_; 
v___x_934_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__27));
v___y_854_ = v___x_934_;
goto v___jp_853_;
}
case 1:
{
lean_object* v___x_935_; 
v___x_935_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__28));
v___y_854_ = v___x_935_;
goto v___jp_853_;
}
case 2:
{
lean_object* v___x_936_; 
v___x_936_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__29));
v___y_854_ = v___x_936_;
goto v___jp_853_;
}
case 3:
{
lean_object* v___x_937_; 
v___x_937_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__30));
v___y_854_ = v___x_937_;
goto v___jp_853_;
}
case 4:
{
lean_object* v___x_938_; 
v___x_938_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__31));
v___y_854_ = v___x_938_;
goto v___jp_853_;
}
case 5:
{
lean_object* v___x_939_; 
v___x_939_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__32));
v___y_854_ = v___x_939_;
goto v___jp_853_;
}
case 6:
{
lean_object* v___x_940_; 
v___x_940_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__33));
v___y_854_ = v___x_940_;
goto v___jp_853_;
}
case 7:
{
lean_object* v___x_941_; 
v___x_941_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__34));
v___y_854_ = v___x_941_;
goto v___jp_853_;
}
case 8:
{
lean_object* v___x_942_; 
v___x_942_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__35));
v___y_854_ = v___x_942_;
goto v___jp_853_;
}
case 9:
{
lean_object* v___x_943_; 
v___x_943_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__36));
v___y_854_ = v___x_943_;
goto v___jp_853_;
}
case 10:
{
lean_object* v___x_944_; 
v___x_944_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__37));
v___y_854_ = v___x_944_;
goto v___jp_853_;
}
case 11:
{
lean_object* v___x_945_; 
v___x_945_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__38));
v___y_854_ = v___x_945_;
goto v___jp_853_;
}
case 12:
{
lean_object* v___x_946_; 
v___x_946_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__39));
v___y_854_ = v___x_946_;
goto v___jp_853_;
}
case 13:
{
lean_object* v___x_947_; 
v___x_947_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__40));
v___y_854_ = v___x_947_;
goto v___jp_853_;
}
case 14:
{
lean_object* v___x_948_; 
v___x_948_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__41));
v___y_854_ = v___x_948_;
goto v___jp_853_;
}
case 15:
{
lean_object* v___x_949_; 
v___x_949_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__42));
v___y_854_ = v___x_949_;
goto v___jp_853_;
}
case 16:
{
lean_object* v___x_950_; 
v___x_950_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__43));
v___y_854_ = v___x_950_;
goto v___jp_853_;
}
case 17:
{
lean_object* v___x_951_; 
v___x_951_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__44));
v___y_854_ = v___x_951_;
goto v___jp_853_;
}
case 18:
{
lean_object* v___x_952_; 
v___x_952_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__45));
v___y_854_ = v___x_952_;
goto v___jp_853_;
}
case 19:
{
lean_object* v___x_953_; 
v___x_953_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__46));
v___y_854_ = v___x_953_;
goto v___jp_853_;
}
case 20:
{
lean_object* v___x_954_; 
v___x_954_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__47));
v___y_854_ = v___x_954_;
goto v___jp_853_;
}
case 21:
{
lean_object* v___x_955_; 
v___x_955_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__48));
v___y_854_ = v___x_955_;
goto v___jp_853_;
}
case 22:
{
lean_object* v___x_956_; 
v___x_956_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__49));
v___y_854_ = v___x_956_;
goto v___jp_853_;
}
case 23:
{
lean_object* v___x_957_; 
v___x_957_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__50));
v___y_854_ = v___x_957_;
goto v___jp_853_;
}
case 24:
{
lean_object* v___x_958_; 
v___x_958_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__51));
v___y_854_ = v___x_958_;
goto v___jp_853_;
}
case 25:
{
lean_object* v___x_959_; 
v___x_959_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__52));
v___y_854_ = v___x_959_;
goto v___jp_853_;
}
case 26:
{
lean_object* v___x_960_; 
v___x_960_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__53));
v___y_854_ = v___x_960_;
goto v___jp_853_;
}
case 27:
{
lean_object* v___x_961_; 
v___x_961_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__54));
v___y_854_ = v___x_961_;
goto v___jp_853_;
}
case 28:
{
lean_object* v___x_962_; 
v___x_962_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__55));
v___y_854_ = v___x_962_;
goto v___jp_853_;
}
case 29:
{
lean_object* v___x_963_; 
v___x_963_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__56));
v___y_854_ = v___x_963_;
goto v___jp_853_;
}
case 30:
{
lean_object* v___x_964_; 
v___x_964_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__57));
v___y_854_ = v___x_964_;
goto v___jp_853_;
}
case 31:
{
lean_object* v___x_965_; 
v___x_965_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__58));
v___y_854_ = v___x_965_;
goto v___jp_853_;
}
case 32:
{
lean_object* v___x_966_; 
v___x_966_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__59));
v___y_854_ = v___x_966_;
goto v___jp_853_;
}
case 33:
{
lean_object* v___x_967_; 
v___x_967_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__60));
v___y_854_ = v___x_967_;
goto v___jp_853_;
}
case 34:
{
lean_object* v___x_968_; 
v___x_968_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__61));
v___y_854_ = v___x_968_;
goto v___jp_853_;
}
case 35:
{
lean_object* v___x_969_; 
v___x_969_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__62));
v___y_854_ = v___x_969_;
goto v___jp_853_;
}
case 36:
{
lean_object* v___x_970_; 
v___x_970_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__63));
v___y_854_ = v___x_970_;
goto v___jp_853_;
}
case 37:
{
lean_object* v___x_971_; 
v___x_971_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__64));
v___y_854_ = v___x_971_;
goto v___jp_853_;
}
case 38:
{
lean_object* v___x_972_; 
v___x_972_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__65));
v___y_854_ = v___x_972_;
goto v___jp_853_;
}
default: 
{
lean_object* v___x_973_; 
v___x_973_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__66));
v___y_854_ = v___x_973_;
goto v___jp_853_;
}
}
v___jp_620_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v_buffer_632_; lean_object* v_buffer_633_; lean_object* v_data_634_; lean_object* v_size_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_644_; 
v___x_624_ = lean_string_to_utf8(v___y_623_);
lean_inc_ref(v___x_624_);
v___x_625_ = lean_array_push(v___y_622_, v___x_624_);
v___x_626_ = lean_byte_array_size(v___x_624_);
lean_dec_ref(v___x_624_);
v___x_627_ = lean_nat_add(v___y_621_, v___x_626_);
lean_dec(v___y_621_);
v___x_628_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__0);
v___x_629_ = lean_array_push(v___x_625_, v___x_628_);
v___x_630_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__1, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__1_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__1);
v___x_631_ = lean_nat_add(v___x_627_, v___x_630_);
lean_dec(v___x_627_);
v_buffer_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_632_, 0, v___x_629_);
lean_ctor_set(v_buffer_632_, 1, v___x_631_);
v_buffer_633_ = l_Std_Http_Headers_fold___redArg(v_headers_619_, v_buffer_632_, v___f_609_);
lean_dec_ref(v_headers_619_);
v_data_634_ = lean_ctor_get(v_buffer_633_, 0);
v_size_635_ = lean_ctor_get(v_buffer_633_, 1);
v_isSharedCheck_644_ = !lean_is_exclusive(v_buffer_633_);
if (v_isSharedCheck_644_ == 0)
{
v___x_637_ = v_buffer_633_;
v_isShared_638_ = v_isSharedCheck_644_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_size_635_);
lean_inc(v_data_634_);
lean_dec(v_buffer_633_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_644_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_639_ = lean_array_push(v_data_634_, v___x_628_);
v___x_640_ = lean_nat_add(v_size_635_, v___x_630_);
lean_dec(v_size_635_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v___x_640_);
lean_ctor_set(v___x_637_, 0, v___x_639_);
v___x_642_ = v___x_637_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
v___jp_645_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_651_ = lean_string_to_utf8(v___y_650_);
lean_dec_ref(v___y_650_);
lean_inc_ref(v___x_651_);
v___x_652_ = lean_array_push(v___y_646_, v___x_651_);
v___x_653_ = lean_byte_array_size(v___x_651_);
lean_dec_ref(v___x_651_);
v___x_654_ = lean_nat_add(v___y_649_, v___x_653_);
lean_dec(v___y_649_);
v___x_655_ = lean_array_push(v___x_652_, v___y_648_);
v___x_656_ = lean_nat_add(v___x_654_, v___y_647_);
lean_dec(v___x_654_);
switch(v_version_617_)
{
case 0:
{
lean_object* v___x_657_; 
v___x_657_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__11));
v___y_621_ = v___x_656_;
v___y_622_ = v___x_655_;
v___y_623_ = v___x_657_;
goto v___jp_620_;
}
case 1:
{
lean_object* v___x_658_; 
v___x_658_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__12));
v___y_621_ = v___x_656_;
v___y_622_ = v___x_655_;
v___y_623_ = v___x_658_;
goto v___jp_620_;
}
case 2:
{
lean_object* v___x_659_; 
v___x_659_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__13));
v___y_621_ = v___x_656_;
v___y_622_ = v___x_655_;
v___y_623_ = v___x_659_;
goto v___jp_620_;
}
default: 
{
lean_object* v___x_660_; 
v___x_660_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__14));
v___y_621_ = v___x_656_;
v___y_622_ = v___x_655_;
v___y_623_ = v___x_660_;
goto v___jp_620_;
}
}
}
v___jp_661_:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_string_append(v___y_666_, v___y_663_);
lean_dec_ref(v___y_663_);
v___x_670_ = lean_string_append(v___x_669_, v___y_668_);
lean_dec_ref(v___y_668_);
v___y_646_ = v___y_662_;
v___y_647_ = v___y_664_;
v___y_648_ = v___y_665_;
v___y_649_ = v___y_667_;
v___y_650_ = v___x_670_;
goto v___jp_645_;
}
v___jp_671_:
{
switch(lean_obj_tag(v_port_672_))
{
case 0:
{
lean_object* v___x_679_; 
v___x_679_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__18));
v___y_662_ = v___y_673_;
v___y_663_ = v___y_678_;
v___y_664_ = v___y_674_;
v___y_665_ = v___y_675_;
v___y_666_ = v___y_676_;
v___y_667_ = v___y_677_;
v___y_668_ = v___x_679_;
goto v___jp_661_;
}
case 1:
{
lean_object* v___x_680_; 
v___x_680_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___y_662_ = v___y_673_;
v___y_663_ = v___y_678_;
v___y_664_ = v___y_674_;
v___y_665_ = v___y_675_;
v___y_666_ = v___y_676_;
v___y_667_ = v___y_677_;
v___y_668_ = v___x_680_;
goto v___jp_661_;
}
default: 
{
uint16_t v_port_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_port_681_ = lean_ctor_get_uint16(v_port_672_, 0);
lean_dec_ref(v_port_672_);
v___x_682_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_683_ = lean_uint16_to_nat(v_port_681_);
v___x_684_ = l_Nat_reprFast(v___x_683_);
v___x_685_ = lean_string_append(v___x_682_, v___x_684_);
lean_dec_ref(v___x_684_);
v___y_662_ = v___y_673_;
v___y_663_ = v___y_678_;
v___y_664_ = v___y_674_;
v___y_665_ = v___y_675_;
v___y_666_ = v___y_676_;
v___y_667_ = v___y_677_;
v___y_668_ = v___x_685_;
goto v___jp_661_;
}
}
}
v___jp_686_:
{
switch(lean_obj_tag(v_host_688_))
{
case 0:
{
lean_object* v_name_694_; 
v_name_694_ = lean_ctor_get(v_host_688_, 0);
lean_inc_ref(v_name_694_);
lean_dec_ref(v_host_688_);
v_port_672_ = v_port_689_;
v___y_673_ = v___y_687_;
v___y_674_ = v___y_690_;
v___y_675_ = v___y_691_;
v___y_676_ = v___y_693_;
v___y_677_ = v___y_692_;
v___y_678_ = v_name_694_;
goto v___jp_671_;
}
case 1:
{
lean_object* v_ipv4_695_; lean_object* v___x_696_; 
v_ipv4_695_ = lean_ctor_get(v_host_688_, 0);
lean_inc_ref(v_ipv4_695_);
lean_dec_ref(v_host_688_);
v___x_696_ = lean_uv_ntop_v4(v_ipv4_695_);
lean_dec_ref(v_ipv4_695_);
v_port_672_ = v_port_689_;
v___y_673_ = v___y_687_;
v___y_674_ = v___y_690_;
v___y_675_ = v___y_691_;
v___y_676_ = v___y_693_;
v___y_677_ = v___y_692_;
v___y_678_ = v___x_696_;
goto v___jp_671_;
}
default: 
{
lean_object* v_ipv6_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_ipv6_697_ = lean_ctor_get(v_host_688_, 0);
lean_inc_ref(v_ipv6_697_);
lean_dec_ref(v_host_688_);
v___x_698_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__21));
v___x_699_ = lean_uv_ntop_v6(v_ipv6_697_);
lean_dec_ref(v_ipv6_697_);
v___x_700_ = lean_string_append(v___x_698_, v___x_699_);
lean_dec_ref(v___x_699_);
v___x_701_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__22));
v___x_702_ = lean_string_append(v___x_700_, v___x_701_);
v_port_672_ = v_port_689_;
v___y_673_ = v___y_687_;
v___y_674_ = v___y_690_;
v___y_675_ = v___y_691_;
v___y_676_ = v___y_693_;
v___y_677_ = v___y_692_;
v___y_678_ = v___x_702_;
goto v___jp_671_;
}
}
}
v___jp_703_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_713_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_714_ = lean_string_append(v___y_705_, v___x_713_);
v___x_715_ = lean_string_append(v___x_714_, v___y_710_);
lean_dec_ref(v___y_710_);
v___x_716_ = lean_string_append(v___x_715_, v___y_707_);
lean_dec_ref(v___y_707_);
v___x_717_ = lean_string_append(v___x_716_, v___y_704_);
lean_dec_ref(v___y_704_);
v___x_718_ = lean_string_append(v___x_717_, v___y_712_);
lean_dec_ref(v___y_712_);
v___y_646_ = v___y_706_;
v___y_647_ = v___y_708_;
v___y_648_ = v___y_709_;
v___y_649_ = v___y_711_;
v___y_650_ = v___x_718_;
goto v___jp_645_;
}
v___jp_719_:
{
if (lean_obj_tag(v___y_720_) == 0)
{
lean_object* v___x_729_; 
v___x_729_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__18));
v___y_704_ = v___y_728_;
v___y_705_ = v___y_721_;
v___y_706_ = v___y_723_;
v___y_707_ = v___y_722_;
v___y_708_ = v___y_724_;
v___y_709_ = v___y_726_;
v___y_710_ = v___y_725_;
v___y_711_ = v___y_727_;
v___y_712_ = v___x_729_;
goto v___jp_703_;
}
else
{
lean_object* v_val_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_val_730_ = lean_ctor_get(v___y_720_, 0);
lean_inc(v_val_730_);
lean_dec_ref(v___y_720_);
v___x_731_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__19));
v___x_732_ = l_Std_Http_URI_EncodedFragment_encode(v_val_730_);
lean_dec(v_val_730_);
v___x_733_ = lean_string_from_utf8_unchecked(v___x_732_);
v___x_734_ = lean_string_append(v___x_731_, v___x_733_);
lean_dec_ref(v___x_733_);
v___y_704_ = v___y_728_;
v___y_705_ = v___y_721_;
v___y_706_ = v___y_723_;
v___y_707_ = v___y_722_;
v___y_708_ = v___y_724_;
v___y_709_ = v___y_726_;
v___y_710_ = v___y_725_;
v___y_711_ = v___y_727_;
v___y_712_ = v___x_734_;
goto v___jp_703_;
}
}
v___jp_735_:
{
lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_745_ = lean_array_get_size(v___y_742_);
v___x_746_ = lean_unsigned_to_nat(0u);
v___x_747_ = lean_nat_dec_eq(v___x_745_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v_encodedParams_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_748_ = lean_array_to_list(v___y_742_);
v___x_749_ = lean_box(0);
v_encodedParams_750_ = l_List_mapTR_loop___redArg(v___f_610_, v___x_748_, v___x_749_);
v___x_751_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__15));
v___x_752_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__16));
v___x_753_ = l_String_intercalate(v___x_752_, v_encodedParams_750_);
v___x_754_ = lean_string_append(v___x_751_, v___x_753_);
lean_dec_ref(v___x_753_);
v___y_720_ = v___y_736_;
v___y_721_ = v___y_737_;
v___y_722_ = v___y_744_;
v___y_723_ = v___y_738_;
v___y_724_ = v___y_739_;
v___y_725_ = v___y_741_;
v___y_726_ = v___y_740_;
v___y_727_ = v___y_743_;
v___y_728_ = v___x_754_;
goto v___jp_719_;
}
else
{
lean_object* v___x_755_; 
lean_dec_ref(v___y_742_);
lean_dec_ref(v___f_610_);
v___x_755_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__18));
v___y_720_ = v___y_736_;
v___y_721_ = v___y_737_;
v___y_722_ = v___y_744_;
v___y_723_ = v___y_738_;
v___y_724_ = v___y_739_;
v___y_725_ = v___y_741_;
v___y_726_ = v___y_740_;
v___y_727_ = v___y_743_;
v___y_728_ = v___x_755_;
goto v___jp_719_;
}
}
v___jp_756_:
{
lean_object* v_segments_766_; uint8_t v_absolute_767_; lean_object* v___x_768_; lean_object* v___x_769_; size_t v_sz_770_; size_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v_result_774_; 
v_segments_766_ = lean_ctor_get(v___y_762_, 0);
lean_inc_ref(v_segments_766_);
v_absolute_767_ = lean_ctor_get_uint8(v___y_762_, sizeof(void*)*1);
lean_dec_ref(v___y_762_);
v___x_768_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__20));
v___x_769_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__10));
v_sz_770_ = lean_array_size(v_segments_766_);
v___x_771_ = ((size_t)0ULL);
v___x_772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_769_, v___f_611_, v_sz_770_, v___x_771_, v_segments_766_);
v___x_773_ = lean_array_to_list(v___x_772_);
v_result_774_ = l_String_intercalate(v___x_768_, v___x_773_);
if (v_absolute_767_ == 0)
{
v___y_736_ = v___y_757_;
v___y_737_ = v___y_758_;
v___y_738_ = v___y_759_;
v___y_739_ = v___y_760_;
v___y_740_ = v___y_761_;
v___y_741_ = v___y_765_;
v___y_742_ = v___y_763_;
v___y_743_ = v___y_764_;
v___y_744_ = v_result_774_;
goto v___jp_735_;
}
else
{
lean_object* v___x_775_; 
v___x_775_ = lean_string_append(v___x_768_, v_result_774_);
lean_dec_ref(v_result_774_);
v___y_736_ = v___y_757_;
v___y_737_ = v___y_758_;
v___y_738_ = v___y_759_;
v___y_739_ = v___y_760_;
v___y_740_ = v___y_761_;
v___y_741_ = v___y_765_;
v___y_742_ = v___y_763_;
v___y_743_ = v___y_764_;
v___y_744_ = v___x_775_;
goto v___jp_735_;
}
}
v___jp_776_:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = lean_string_append(v___y_783_, v___y_782_);
lean_dec_ref(v___y_782_);
v___x_790_ = lean_string_append(v___x_789_, v___y_788_);
lean_dec_ref(v___y_788_);
lean_inc_ref(v___y_777_);
v___x_791_ = lean_string_append(v___y_777_, v___x_790_);
lean_dec_ref(v___x_790_);
v___y_757_ = v___y_778_;
v___y_758_ = v___y_779_;
v___y_759_ = v___y_780_;
v___y_760_ = v___y_781_;
v___y_761_ = v___y_784_;
v___y_762_ = v___y_785_;
v___y_763_ = v___y_786_;
v___y_764_ = v___y_787_;
v___y_765_ = v___x_791_;
goto v___jp_756_;
}
v___jp_792_:
{
switch(lean_obj_tag(v_port_796_))
{
case 0:
{
lean_object* v___x_805_; 
v___x_805_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__18));
v___y_777_ = v___y_793_;
v___y_778_ = v___y_794_;
v___y_779_ = v___y_795_;
v___y_780_ = v___y_797_;
v___y_781_ = v___y_798_;
v___y_782_ = v___y_804_;
v___y_783_ = v___y_799_;
v___y_784_ = v___y_800_;
v___y_785_ = v___y_801_;
v___y_786_ = v___y_802_;
v___y_787_ = v___y_803_;
v___y_788_ = v___x_805_;
goto v___jp_776_;
}
case 1:
{
lean_object* v___x_806_; 
v___x_806_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___y_777_ = v___y_793_;
v___y_778_ = v___y_794_;
v___y_779_ = v___y_795_;
v___y_780_ = v___y_797_;
v___y_781_ = v___y_798_;
v___y_782_ = v___y_804_;
v___y_783_ = v___y_799_;
v___y_784_ = v___y_800_;
v___y_785_ = v___y_801_;
v___y_786_ = v___y_802_;
v___y_787_ = v___y_803_;
v___y_788_ = v___x_806_;
goto v___jp_776_;
}
default: 
{
uint16_t v_port_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_port_807_ = lean_ctor_get_uint16(v_port_796_, 0);
lean_dec_ref(v_port_796_);
v___x_808_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_809_ = lean_uint16_to_nat(v_port_807_);
v___x_810_ = l_Nat_reprFast(v___x_809_);
v___x_811_ = lean_string_append(v___x_808_, v___x_810_);
lean_dec_ref(v___x_810_);
v___y_777_ = v___y_793_;
v___y_778_ = v___y_794_;
v___y_779_ = v___y_795_;
v___y_780_ = v___y_797_;
v___y_781_ = v___y_798_;
v___y_782_ = v___y_804_;
v___y_783_ = v___y_799_;
v___y_784_ = v___y_800_;
v___y_785_ = v___y_801_;
v___y_786_ = v___y_802_;
v___y_787_ = v___y_803_;
v___y_788_ = v___x_811_;
goto v___jp_776_;
}
}
}
v___jp_812_:
{
switch(lean_obj_tag(v_host_817_))
{
case 0:
{
lean_object* v_name_825_; 
v_name_825_ = lean_ctor_get(v_host_817_, 0);
lean_inc_ref(v_name_825_);
lean_dec_ref(v_host_817_);
v___y_793_ = v___y_813_;
v___y_794_ = v___y_814_;
v___y_795_ = v___y_815_;
v_port_796_ = v_port_818_;
v___y_797_ = v___y_816_;
v___y_798_ = v___y_819_;
v___y_799_ = v___y_824_;
v___y_800_ = v___y_820_;
v___y_801_ = v___y_821_;
v___y_802_ = v___y_822_;
v___y_803_ = v___y_823_;
v___y_804_ = v_name_825_;
goto v___jp_792_;
}
case 1:
{
lean_object* v_ipv4_826_; lean_object* v___x_827_; 
v_ipv4_826_ = lean_ctor_get(v_host_817_, 0);
lean_inc_ref(v_ipv4_826_);
lean_dec_ref(v_host_817_);
v___x_827_ = lean_uv_ntop_v4(v_ipv4_826_);
lean_dec_ref(v_ipv4_826_);
v___y_793_ = v___y_813_;
v___y_794_ = v___y_814_;
v___y_795_ = v___y_815_;
v_port_796_ = v_port_818_;
v___y_797_ = v___y_816_;
v___y_798_ = v___y_819_;
v___y_799_ = v___y_824_;
v___y_800_ = v___y_820_;
v___y_801_ = v___y_821_;
v___y_802_ = v___y_822_;
v___y_803_ = v___y_823_;
v___y_804_ = v___x_827_;
goto v___jp_792_;
}
default: 
{
lean_object* v_ipv6_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_ipv6_828_ = lean_ctor_get(v_host_817_, 0);
lean_inc_ref(v_ipv6_828_);
lean_dec_ref(v_host_817_);
v___x_829_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__21));
v___x_830_ = lean_uv_ntop_v6(v_ipv6_828_);
lean_dec_ref(v_ipv6_828_);
v___x_831_ = lean_string_append(v___x_829_, v___x_830_);
lean_dec_ref(v___x_830_);
v___x_832_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__22));
v___x_833_ = lean_string_append(v___x_831_, v___x_832_);
v___y_793_ = v___y_813_;
v___y_794_ = v___y_814_;
v___y_795_ = v___y_815_;
v_port_796_ = v_port_818_;
v___y_797_ = v___y_816_;
v___y_798_ = v___y_819_;
v___y_799_ = v___y_824_;
v___y_800_ = v___y_820_;
v___y_801_ = v___y_821_;
v___y_802_ = v___y_822_;
v___y_803_ = v___y_823_;
v___y_804_ = v___x_833_;
goto v___jp_792_;
}
}
}
v___jp_834_:
{
if (lean_obj_tag(v___y_836_) == 0)
{
lean_dec_ref(v___f_612_);
v___y_646_ = v___y_835_;
v___y_647_ = v___y_837_;
v___y_648_ = v___y_838_;
v___y_649_ = v___y_839_;
v___y_650_ = v___y_840_;
goto v___jp_645_;
}
else
{
lean_object* v_val_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v_val_841_ = lean_ctor_get(v___y_836_, 0);
lean_inc(v_val_841_);
lean_dec_ref(v___y_836_);
v___x_842_ = lean_array_get_size(v_val_841_);
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = lean_nat_dec_eq(v___x_842_, v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v_encodedParams_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_845_ = lean_array_to_list(v_val_841_);
v___x_846_ = lean_box(0);
v_encodedParams_847_ = l_List_mapTR_loop___redArg(v___f_612_, v___x_845_, v___x_846_);
v___x_848_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__15));
v___x_849_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__16));
v___x_850_ = l_String_intercalate(v___x_849_, v_encodedParams_847_);
v___x_851_ = lean_string_append(v___x_848_, v___x_850_);
lean_dec_ref(v___x_850_);
v___x_852_ = lean_string_append(v___y_840_, v___x_851_);
lean_dec_ref(v___x_851_);
v___y_646_ = v___y_835_;
v___y_647_ = v___y_837_;
v___y_648_ = v___y_838_;
v___y_649_ = v___y_839_;
v___y_650_ = v___x_852_;
goto v___jp_645_;
}
else
{
lean_dec(v_val_841_);
lean_dec_ref(v___f_612_);
v___y_646_ = v___y_835_;
v___y_647_ = v___y_837_;
v___y_648_ = v___y_838_;
v___y_649_ = v___y_839_;
v___y_650_ = v___y_840_;
goto v___jp_645_;
}
}
}
v___jp_853_:
{
lean_object* v_data_855_; lean_object* v_size_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_data_855_ = lean_ctor_get(v_buffer_614_, 0);
lean_inc_ref(v_data_855_);
v_size_856_ = lean_ctor_get(v_buffer_614_, 1);
lean_inc(v_size_856_);
lean_dec_ref(v_buffer_614_);
v___x_857_ = lean_string_to_utf8(v___y_854_);
lean_inc_ref(v___x_857_);
v___x_858_ = lean_array_push(v_data_855_, v___x_857_);
v___x_859_ = lean_byte_array_size(v___x_857_);
lean_dec_ref(v___x_857_);
v___x_860_ = lean_nat_add(v_size_856_, v___x_859_);
lean_dec(v_size_856_);
v___x_861_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__3);
v___x_862_ = lean_array_push(v___x_858_, v___x_861_);
v___x_863_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__2___closed__4, &l_Std_Http_Request_instEncodeV11Head___lam__2___closed__4_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__2___closed__4);
v___x_864_ = lean_nat_add(v___x_860_, v___x_863_);
lean_dec(v___x_860_);
switch(lean_obj_tag(v_uri_618_))
{
case 0:
{
lean_object* v_path_865_; lean_object* v_query_866_; lean_object* v_segments_867_; uint8_t v_absolute_868_; lean_object* v___x_869_; lean_object* v___x_870_; size_t v_sz_871_; size_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v_result_875_; 
lean_dec_ref(v___f_611_);
lean_dec_ref(v___f_610_);
v_path_865_ = lean_ctor_get(v_uri_618_, 0);
lean_inc_ref(v_path_865_);
v_query_866_ = lean_ctor_get(v_uri_618_, 1);
lean_inc(v_query_866_);
lean_dec_ref(v_uri_618_);
v_segments_867_ = lean_ctor_get(v_path_865_, 0);
lean_inc_ref(v_segments_867_);
v_absolute_868_ = lean_ctor_get_uint8(v_path_865_, sizeof(void*)*1);
lean_dec_ref(v_path_865_);
v___x_869_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__20));
v___x_870_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__10));
v_sz_871_ = lean_array_size(v_segments_867_);
v___x_872_ = ((size_t)0ULL);
v___x_873_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_870_, v___f_613_, v_sz_871_, v___x_872_, v_segments_867_);
v___x_874_ = lean_array_to_list(v___x_873_);
v_result_875_ = l_String_intercalate(v___x_869_, v___x_874_);
if (v_absolute_868_ == 0)
{
v___y_835_ = v___x_862_;
v___y_836_ = v_query_866_;
v___y_837_ = v___x_863_;
v___y_838_ = v___x_861_;
v___y_839_ = v___x_864_;
v___y_840_ = v_result_875_;
goto v___jp_834_;
}
else
{
lean_object* v___x_876_; 
v___x_876_ = lean_string_append(v___x_869_, v_result_875_);
lean_dec_ref(v_result_875_);
v___y_835_ = v___x_862_;
v___y_836_ = v_query_866_;
v___y_837_ = v___x_863_;
v___y_838_ = v___x_861_;
v___y_839_ = v___x_864_;
v___y_840_ = v___x_876_;
goto v___jp_834_;
}
}
case 1:
{
lean_object* v_uri_877_; lean_object* v_authority_878_; 
lean_dec_ref(v___f_613_);
lean_dec_ref(v___f_612_);
v_uri_877_ = lean_ctor_get(v_uri_618_, 0);
lean_inc_ref(v_uri_877_);
lean_dec_ref(v_uri_618_);
v_authority_878_ = lean_ctor_get(v_uri_877_, 1);
if (lean_obj_tag(v_authority_878_) == 0)
{
lean_object* v_scheme_879_; lean_object* v_path_880_; lean_object* v_query_881_; lean_object* v_fragment_882_; lean_object* v___x_883_; 
v_scheme_879_ = lean_ctor_get(v_uri_877_, 0);
lean_inc_ref(v_scheme_879_);
v_path_880_ = lean_ctor_get(v_uri_877_, 2);
lean_inc_ref(v_path_880_);
v_query_881_ = lean_ctor_get(v_uri_877_, 3);
lean_inc_ref(v_query_881_);
v_fragment_882_ = lean_ctor_get(v_uri_877_, 4);
lean_inc(v_fragment_882_);
lean_dec_ref(v_uri_877_);
v___x_883_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__18));
v___y_757_ = v_fragment_882_;
v___y_758_ = v_scheme_879_;
v___y_759_ = v___x_862_;
v___y_760_ = v___x_863_;
v___y_761_ = v___x_861_;
v___y_762_ = v_path_880_;
v___y_763_ = v_query_881_;
v___y_764_ = v___x_864_;
v___y_765_ = v___x_883_;
goto v___jp_756_;
}
else
{
lean_object* v_val_884_; lean_object* v_scheme_885_; lean_object* v_path_886_; lean_object* v_query_887_; lean_object* v_fragment_888_; lean_object* v_userInfo_889_; lean_object* v_host_890_; lean_object* v_port_891_; lean_object* v___x_892_; 
v_val_884_ = lean_ctor_get(v_authority_878_, 0);
lean_inc(v_val_884_);
v_scheme_885_ = lean_ctor_get(v_uri_877_, 0);
lean_inc_ref(v_scheme_885_);
v_path_886_ = lean_ctor_get(v_uri_877_, 2);
lean_inc_ref(v_path_886_);
v_query_887_ = lean_ctor_get(v_uri_877_, 3);
lean_inc_ref(v_query_887_);
v_fragment_888_ = lean_ctor_get(v_uri_877_, 4);
lean_inc(v_fragment_888_);
lean_dec_ref(v_uri_877_);
v_userInfo_889_ = lean_ctor_get(v_val_884_, 0);
lean_inc(v_userInfo_889_);
v_host_890_ = lean_ctor_get(v_val_884_, 1);
lean_inc_ref(v_host_890_);
v_port_891_ = lean_ctor_get(v_val_884_, 2);
lean_inc(v_port_891_);
lean_dec(v_val_884_);
v___x_892_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__24));
if (lean_obj_tag(v_userInfo_889_) == 0)
{
lean_object* v___x_893_; 
v___x_893_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__18));
v___y_813_ = v___x_892_;
v___y_814_ = v_fragment_888_;
v___y_815_ = v_scheme_885_;
v___y_816_ = v___x_862_;
v_host_817_ = v_host_890_;
v_port_818_ = v_port_891_;
v___y_819_ = v___x_863_;
v___y_820_ = v___x_861_;
v___y_821_ = v_path_886_;
v___y_822_ = v_query_887_;
v___y_823_ = v___x_864_;
v___y_824_ = v___x_893_;
goto v___jp_812_;
}
else
{
lean_object* v_val_894_; lean_object* v_password_895_; 
v_val_894_ = lean_ctor_get(v_userInfo_889_, 0);
lean_inc(v_val_894_);
lean_dec_ref(v_userInfo_889_);
v_password_895_ = lean_ctor_get(v_val_894_, 1);
if (lean_obj_tag(v_password_895_) == 0)
{
lean_object* v_username_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_username_896_ = lean_ctor_get(v_val_894_, 0);
lean_inc_ref(v_username_896_);
lean_dec(v_val_894_);
v___x_897_ = lean_string_from_utf8_unchecked(v_username_896_);
v___x_898_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__25));
v___x_899_ = lean_string_append(v___x_897_, v___x_898_);
v___y_813_ = v___x_892_;
v___y_814_ = v_fragment_888_;
v___y_815_ = v_scheme_885_;
v___y_816_ = v___x_862_;
v_host_817_ = v_host_890_;
v_port_818_ = v_port_891_;
v___y_819_ = v___x_863_;
v___y_820_ = v___x_861_;
v___y_821_ = v_path_886_;
v___y_822_ = v_query_887_;
v___y_823_ = v___x_864_;
v___y_824_ = v___x_899_;
goto v___jp_812_;
}
else
{
lean_object* v_username_900_; lean_object* v_val_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_inc_ref(v_password_895_);
v_username_900_ = lean_ctor_get(v_val_894_, 0);
lean_inc_ref(v_username_900_);
lean_dec(v_val_894_);
v_val_901_ = lean_ctor_get(v_password_895_, 0);
lean_inc(v_val_901_);
lean_dec_ref(v_password_895_);
v___x_902_ = lean_string_from_utf8_unchecked(v_username_900_);
v___x_903_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_904_ = lean_string_append(v___x_902_, v___x_903_);
v___x_905_ = lean_string_from_utf8_unchecked(v_val_901_);
v___x_906_ = lean_string_append(v___x_904_, v___x_905_);
lean_dec_ref(v___x_905_);
v___x_907_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__25));
v___x_908_ = lean_string_append(v___x_906_, v___x_907_);
v___y_813_ = v___x_892_;
v___y_814_ = v_fragment_888_;
v___y_815_ = v_scheme_885_;
v___y_816_ = v___x_862_;
v_host_817_ = v_host_890_;
v_port_818_ = v_port_891_;
v___y_819_ = v___x_863_;
v___y_820_ = v___x_861_;
v___y_821_ = v_path_886_;
v___y_822_ = v_query_887_;
v___y_823_ = v___x_864_;
v___y_824_ = v___x_908_;
goto v___jp_812_;
}
}
}
}
case 2:
{
lean_object* v_authority_909_; lean_object* v_userInfo_910_; 
lean_dec_ref(v___f_613_);
lean_dec_ref(v___f_612_);
lean_dec_ref(v___f_611_);
lean_dec_ref(v___f_610_);
v_authority_909_ = lean_ctor_get(v_uri_618_, 0);
lean_inc_ref(v_authority_909_);
lean_dec_ref(v_uri_618_);
v_userInfo_910_ = lean_ctor_get(v_authority_909_, 0);
if (lean_obj_tag(v_userInfo_910_) == 0)
{
lean_object* v_host_911_; lean_object* v_port_912_; lean_object* v___x_913_; 
v_host_911_ = lean_ctor_get(v_authority_909_, 1);
lean_inc_ref(v_host_911_);
v_port_912_ = lean_ctor_get(v_authority_909_, 2);
lean_inc(v_port_912_);
lean_dec_ref(v_authority_909_);
v___x_913_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__18));
v___y_687_ = v___x_862_;
v_host_688_ = v_host_911_;
v_port_689_ = v_port_912_;
v___y_690_ = v___x_863_;
v___y_691_ = v___x_861_;
v___y_692_ = v___x_864_;
v___y_693_ = v___x_913_;
goto v___jp_686_;
}
else
{
lean_object* v_val_914_; lean_object* v_password_915_; 
v_val_914_ = lean_ctor_get(v_userInfo_910_, 0);
lean_inc(v_val_914_);
v_password_915_ = lean_ctor_get(v_val_914_, 1);
if (lean_obj_tag(v_password_915_) == 0)
{
lean_object* v_host_916_; lean_object* v_port_917_; lean_object* v_username_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_host_916_ = lean_ctor_get(v_authority_909_, 1);
lean_inc_ref(v_host_916_);
v_port_917_ = lean_ctor_get(v_authority_909_, 2);
lean_inc(v_port_917_);
lean_dec_ref(v_authority_909_);
v_username_918_ = lean_ctor_get(v_val_914_, 0);
lean_inc_ref(v_username_918_);
lean_dec(v_val_914_);
v___x_919_ = lean_string_from_utf8_unchecked(v_username_918_);
v___x_920_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__25));
v___x_921_ = lean_string_append(v___x_919_, v___x_920_);
v___y_687_ = v___x_862_;
v_host_688_ = v_host_916_;
v_port_689_ = v_port_917_;
v___y_690_ = v___x_863_;
v___y_691_ = v___x_861_;
v___y_692_ = v___x_864_;
v___y_693_ = v___x_921_;
goto v___jp_686_;
}
else
{
lean_object* v_host_922_; lean_object* v_port_923_; lean_object* v_username_924_; lean_object* v_val_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
lean_inc_ref(v_password_915_);
v_host_922_ = lean_ctor_get(v_authority_909_, 1);
lean_inc_ref(v_host_922_);
v_port_923_ = lean_ctor_get(v_authority_909_, 2);
lean_inc(v_port_923_);
lean_dec_ref(v_authority_909_);
v_username_924_ = lean_ctor_get(v_val_914_, 0);
lean_inc_ref(v_username_924_);
lean_dec(v_val_914_);
v_val_925_ = lean_ctor_get(v_password_915_, 0);
lean_inc(v_val_925_);
lean_dec_ref(v_password_915_);
v___x_926_ = lean_string_from_utf8_unchecked(v_username_924_);
v___x_927_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__17));
v___x_928_ = lean_string_append(v___x_926_, v___x_927_);
v___x_929_ = lean_string_from_utf8_unchecked(v_val_925_);
v___x_930_ = lean_string_append(v___x_928_, v___x_929_);
lean_dec_ref(v___x_929_);
v___x_931_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__25));
v___x_932_ = lean_string_append(v___x_930_, v___x_931_);
v___y_687_ = v___x_862_;
v_host_688_ = v_host_922_;
v_port_689_ = v_port_923_;
v___y_690_ = v___x_863_;
v___y_691_ = v___x_861_;
v___y_692_ = v___x_864_;
v___y_693_ = v___x_932_;
goto v___jp_686_;
}
}
}
default: 
{
lean_object* v___x_933_; 
lean_dec_ref(v___f_613_);
lean_dec_ref(v___f_612_);
lean_dec_ref(v___f_611_);
lean_dec_ref(v___f_610_);
v___x_933_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__6___closed__26));
v___y_646_ = v___x_862_;
v___y_647_ = v___x_863_;
v___y_648_ = v___x_861_;
v___y_649_ = v___x_864_;
v___y_650_ = v___x_933_;
goto v___jp_645_;
}
}
}
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__0(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; uint8_t v___x_984_; lean_object* v___x_985_; 
v___x_981_ = l_Std_Http_Headers_empty;
v___x_982_ = lean_box(3);
v___x_983_ = 1;
v___x_984_ = 8;
v___x_985_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_985_, 0, v___x_982_);
lean_ctor_set(v___x_985_, 1, v___x_981_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*2, v___x_984_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*2 + 1, v___x_983_);
return v___x_985_;
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__1(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_986_ = l_Std_Http_Extensions_empty;
v___x_987_ = lean_obj_once(&l_Std_Http_Request_new___closed__0, &l_Std_Http_Request_new___closed__0_once, _init_l_Std_Http_Request_new___closed__0);
v___x_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_986_);
return v___x_988_;
}
}
static lean_object* _init_l_Std_Http_Request_new(void){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = lean_obj_once(&l_Std_Http_Request_new___closed__1, &l_Std_Http_Request_new___closed__1_once, _init_l_Std_Http_Request_new___closed__1);
return v___x_989_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_empty(void){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = lean_obj_once(&l_Std_Http_Request_new___closed__1, &l_Std_Http_Request_new___closed__1_once, _init_l_Std_Http_Request_new___closed__1);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method(lean_object* v_builder_991_, uint8_t v_method_992_){
_start:
{
lean_object* v_line_993_; lean_object* v_extensions_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1011_; 
v_line_993_ = lean_ctor_get(v_builder_991_, 0);
v_extensions_994_ = lean_ctor_get(v_builder_991_, 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_builder_991_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_996_ = v_builder_991_;
v_isShared_997_ = v_isSharedCheck_1011_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_extensions_994_);
lean_inc(v_line_993_);
lean_dec(v_builder_991_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1011_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
uint8_t v_version_998_; lean_object* v_uri_999_; lean_object* v_headers_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1010_; 
v_version_998_ = lean_ctor_get_uint8(v_line_993_, sizeof(void*)*2 + 1);
v_uri_999_ = lean_ctor_get(v_line_993_, 0);
v_headers_1000_ = lean_ctor_get(v_line_993_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_line_993_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1002_ = v_line_993_;
v_isShared_1003_ = v_isSharedCheck_1010_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_headers_1000_);
lean_inc(v_uri_999_);
lean_dec(v_line_993_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1010_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_uri_999_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_headers_1000_);
lean_ctor_set_uint8(v_reuseFailAlloc_1009_, sizeof(void*)*2 + 1, v_version_998_);
v___x_1005_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*2, v_method_992_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1005_);
v___x_1007_ = v___x_996_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_extensions_994_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method___boxed(lean_object* v_builder_1012_, lean_object* v_method_1013_){
_start:
{
uint8_t v_method_boxed_1014_; lean_object* v_res_1015_; 
v_method_boxed_1014_ = lean_unbox(v_method_1013_);
v_res_1015_ = l_Std_Http_Request_Builder_method(v_builder_1012_, v_method_boxed_1014_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version(lean_object* v_builder_1016_, uint8_t v_version_1017_){
_start:
{
lean_object* v_line_1018_; lean_object* v_extensions_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1036_; 
v_line_1018_ = lean_ctor_get(v_builder_1016_, 0);
v_extensions_1019_ = lean_ctor_get(v_builder_1016_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_builder_1016_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1021_ = v_builder_1016_;
v_isShared_1022_ = v_isSharedCheck_1036_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_extensions_1019_);
lean_inc(v_line_1018_);
lean_dec(v_builder_1016_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1036_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
uint8_t v_method_1023_; lean_object* v_uri_1024_; lean_object* v_headers_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1035_; 
v_method_1023_ = lean_ctor_get_uint8(v_line_1018_, sizeof(void*)*2);
v_uri_1024_ = lean_ctor_get(v_line_1018_, 0);
v_headers_1025_ = lean_ctor_get(v_line_1018_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_line_1018_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1027_ = v_line_1018_;
v_isShared_1028_ = v_isSharedCheck_1035_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_headers_1025_);
lean_inc(v_uri_1024_);
lean_dec(v_line_1018_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1035_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_uri_1024_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_headers_1025_);
lean_ctor_set_uint8(v_reuseFailAlloc_1034_, sizeof(void*)*2, v_method_1023_);
v___x_1030_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
lean_ctor_set_uint8(v___x_1030_, sizeof(void*)*2 + 1, v_version_1017_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1030_);
v___x_1032_ = v___x_1021_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_extensions_1019_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version___boxed(lean_object* v_builder_1037_, lean_object* v_version_1038_){
_start:
{
uint8_t v_version_boxed_1039_; lean_object* v_res_1040_; 
v_version_boxed_1039_ = lean_unbox(v_version_1038_);
v_res_1040_ = l_Std_Http_Request_Builder_version(v_builder_1037_, v_version_boxed_1039_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri(lean_object* v_builder_1041_, lean_object* v_uri_1042_){
_start:
{
lean_object* v_line_1043_; lean_object* v_extensions_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1062_; 
v_line_1043_ = lean_ctor_get(v_builder_1041_, 0);
v_extensions_1044_ = lean_ctor_get(v_builder_1041_, 1);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_builder_1041_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1046_ = v_builder_1041_;
v_isShared_1047_ = v_isSharedCheck_1062_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_extensions_1044_);
lean_inc(v_line_1043_);
lean_dec(v_builder_1041_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1062_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
uint8_t v_method_1048_; uint8_t v_version_1049_; lean_object* v_headers_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1060_; 
v_method_1048_ = lean_ctor_get_uint8(v_line_1043_, sizeof(void*)*2);
v_version_1049_ = lean_ctor_get_uint8(v_line_1043_, sizeof(void*)*2 + 1);
v_headers_1050_ = lean_ctor_get(v_line_1043_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_line_1043_);
if (v_isSharedCheck_1060_ == 0)
{
lean_object* v_unused_1061_; 
v_unused_1061_ = lean_ctor_get(v_line_1043_, 0);
lean_dec(v_unused_1061_);
v___x_1052_ = v_line_1043_;
v_isShared_1053_ = v_isSharedCheck_1060_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_headers_1050_);
lean_dec(v_line_1043_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1060_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v_uri_1042_);
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_uri_1042_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_headers_1050_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, sizeof(void*)*2, v_method_1048_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, sizeof(void*)*2 + 1, v_version_1049_);
v___x_1055_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1057_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1055_);
v___x_1057_ = v___x_1046_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_extensions_1044_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(lean_object* v_msg_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = l_Std_Http_instInhabitedRequestTarget_default;
v___x_1065_ = lean_panic_fn_borrowed(v___x_1064_, v_msg_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___lam__0(lean_object* v___x_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_1069_, v___y_1070_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_pos_1072_; lean_object* v_array_1073_; lean_object* v_idx_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v_pos_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_pos_1072_);
v_array_1073_ = lean_ctor_get(v_pos_1072_, 0);
v_idx_1074_ = lean_ctor_get(v_pos_1072_, 1);
v___x_1075_ = lean_byte_array_size(v_array_1073_);
v___x_1076_ = lean_nat_dec_lt(v_idx_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_dec(v_pos_1072_);
return v___x_1071_;
}
else
{
lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1084_; 
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; lean_object* v_unused_1086_; 
v_unused_1085_ = lean_ctor_get(v___x_1071_, 1);
lean_dec(v_unused_1085_);
v_unused_1086_ = lean_ctor_get(v___x_1071_, 0);
lean_dec(v_unused_1086_);
v___x_1078_ = v___x_1071_;
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
else
{
lean_dec(v___x_1071_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___lam__0___closed__1));
if (v_isShared_1079_ == 0)
{
lean_ctor_set_tag(v___x_1078_, 1);
lean_ctor_set(v___x_1078_, 1, v___x_1080_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_pos_1072_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
else
{
return v___x_1071_;
}
}
}
static lean_object* _init_l_Std_Http_Request_Builder_uri_x21___closed__5(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1100_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__4));
v___x_1101_ = lean_unsigned_to_nat(12u);
v___x_1102_ = lean_unsigned_to_nat(45u);
v___x_1103_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__3));
v___x_1104_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__2));
v___x_1105_ = l_mkPanicMessageWithDecl(v___x_1104_, v___x_1103_, v___x_1102_, v___x_1101_, v___x_1100_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21(lean_object* v_builder_1106_, lean_object* v_uri_1107_){
_start:
{
lean_object* v___y_1109_; lean_object* v___f_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___f_1130_ = ((lean_object*)(l_Std_Http_Request_Builder_uri_x21___closed__1));
v___x_1131_ = lean_string_to_utf8(v_uri_1107_);
v___x_1132_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1130_, v___x_1131_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec_ref(v___x_1132_);
v___x_1133_ = lean_obj_once(&l_Std_Http_Request_Builder_uri_x21___closed__5, &l_Std_Http_Request_Builder_uri_x21___closed__5_once, _init_l_Std_Http_Request_Builder_uri_x21___closed__5);
v___x_1134_ = l_panic___at___00Std_Http_Request_Builder_uri_x21_spec__0(v___x_1133_);
v___y_1109_ = v___x_1134_;
goto v___jp_1108_;
}
else
{
lean_object* v_a_1135_; 
v_a_1135_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1135_);
lean_dec_ref(v___x_1132_);
v___y_1109_ = v_a_1135_;
goto v___jp_1108_;
}
v___jp_1108_:
{
lean_object* v_line_1110_; lean_object* v_extensions_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1129_; 
v_line_1110_ = lean_ctor_get(v_builder_1106_, 0);
v_extensions_1111_ = lean_ctor_get(v_builder_1106_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_builder_1106_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1113_ = v_builder_1106_;
v_isShared_1114_ = v_isSharedCheck_1129_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_extensions_1111_);
lean_inc(v_line_1110_);
lean_dec(v_builder_1106_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1129_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
uint8_t v_method_1115_; uint8_t v_version_1116_; lean_object* v_headers_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1127_; 
v_method_1115_ = lean_ctor_get_uint8(v_line_1110_, sizeof(void*)*2);
v_version_1116_ = lean_ctor_get_uint8(v_line_1110_, sizeof(void*)*2 + 1);
v_headers_1117_ = lean_ctor_get(v_line_1110_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_line_1110_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; 
v_unused_1128_ = lean_ctor_get(v_line_1110_, 0);
lean_dec(v_unused_1128_);
v___x_1119_ = v_line_1110_;
v_isShared_1120_ = v_isSharedCheck_1127_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_headers_1117_);
lean_dec(v_line_1110_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1127_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___y_1109_);
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___y_1109_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_headers_1117_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*2, v_method_1115_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*2 + 1, v_version_1116_);
v___x_1122_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1124_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1122_);
v___x_1124_ = v___x_1113_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_extensions_1111_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri_x21___boxed(lean_object* v_builder_1136_, lean_object* v_uri_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Std_Http_Request_Builder_uri_x21(v_builder_1136_, v_uri_1137_);
lean_dec_ref(v_uri_1137_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headers(lean_object* v_builder_1139_, lean_object* v_headers_1140_){
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
uint8_t v_method_1146_; uint8_t v_version_1147_; lean_object* v_uri_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1158_; 
v_method_1146_ = lean_ctor_get_uint8(v_line_1141_, sizeof(void*)*2);
v_version_1147_ = lean_ctor_get_uint8(v_line_1141_, sizeof(void*)*2 + 1);
v_uri_1148_ = lean_ctor_get(v_line_1141_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_line_1141_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; 
v_unused_1159_ = lean_ctor_get(v_line_1141_, 1);
lean_dec(v_unused_1159_);
v___x_1150_ = v_line_1141_;
v_isShared_1151_ = v_isSharedCheck_1158_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_uri_1148_);
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
lean_ctor_set(v___x_1150_, 1, v_headers_1140_);
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_uri_1148_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_headers_1140_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(lean_object* v_i_1161_, lean_object* v_x_1162_){
_start:
{
if (lean_obj_tag(v_x_1162_) == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_mk_empty_array_with_capacity(v___x_1163_);
v___x_1165_ = lean_array_push(v___x_1164_, v_i_1161_);
v___x_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
else
{
lean_object* v_val_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1175_; 
v_val_1167_ = lean_ctor_get(v_x_1162_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_x_1162_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1169_ = v_x_1162_;
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_val_1167_);
lean_dec(v_x_1162_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1171_ = lean_array_push(v_val_1167_, v_i_1161_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1171_);
v___x_1173_ = v___x_1169_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(lean_object* v_i_1176_, lean_object* v_a_1177_, lean_object* v_x_1178_){
_start:
{
if (lean_obj_tag(v_x_1178_) == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v_val_1181_; lean_object* v___x_1182_; 
v___x_1179_ = lean_box(0);
v___x_1180_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(v_i_1176_, v___x_1179_);
v_val_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_val_1181_);
lean_dec(v___x_1180_);
v___x_1182_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1182_, 0, v_a_1177_);
lean_ctor_set(v___x_1182_, 1, v_val_1181_);
lean_ctor_set(v___x_1182_, 2, v_x_1178_);
return v___x_1182_;
}
else
{
lean_object* v_key_1183_; lean_object* v_value_1184_; lean_object* v_tail_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1200_; 
v_key_1183_ = lean_ctor_get(v_x_1178_, 0);
v_value_1184_ = lean_ctor_get(v_x_1178_, 1);
v_tail_1185_ = lean_ctor_get(v_x_1178_, 2);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_x_1178_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1187_ = v_x_1178_;
v_isShared_1188_ = v_isSharedCheck_1200_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_tail_1185_);
lean_inc(v_value_1184_);
lean_inc(v_key_1183_);
lean_dec(v_x_1178_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1200_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_string_dec_eq(v_key_1183_, v_a_1177_);
if (v___x_1189_ == 0)
{
lean_object* v_tail_1190_; lean_object* v___x_1192_; 
v_tail_1190_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_1176_, v_a_1177_, v_tail_1185_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 2, v_tail_1190_);
v___x_1192_ = v___x_1187_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_key_1183_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_value_1184_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_tail_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v_val_1196_; lean_object* v___x_1198_; 
lean_dec(v_key_1183_);
v___x_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_value_1184_);
v___x_1195_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(v_i_1176_, v___x_1194_);
v_val_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_val_1196_);
lean_dec(v___x_1195_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 1, v_val_1196_);
lean_ctor_set(v___x_1187_, 0, v_a_1177_);
v___x_1198_ = v___x_1187_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1177_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_val_1196_);
lean_ctor_set(v_reuseFailAlloc_1199_, 2, v_tail_1185_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(lean_object* v_a_1201_, lean_object* v_x_1202_){
_start:
{
if (lean_obj_tag(v_x_1202_) == 0)
{
uint8_t v___x_1203_; 
v___x_1203_ = 0;
return v___x_1203_;
}
else
{
lean_object* v_key_1204_; lean_object* v_tail_1205_; uint8_t v___x_1206_; 
v_key_1204_ = lean_ctor_get(v_x_1202_, 0);
v_tail_1205_ = lean_ctor_get(v_x_1202_, 2);
v___x_1206_ = lean_string_dec_eq(v_key_1204_, v_a_1201_);
if (v___x_1206_ == 0)
{
v_x_1202_ = v_tail_1205_;
goto _start;
}
else
{
return v___x_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg___boxed(lean_object* v_a_1208_, lean_object* v_x_1209_){
_start:
{
uint8_t v_res_1210_; lean_object* v_r_1211_; 
v_res_1210_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1208_, v_x_1209_);
lean_dec(v_x_1209_);
lean_dec_ref(v_a_1208_);
v_r_1211_ = lean_box(v_res_1210_);
return v_r_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1212_, lean_object* v_x_1213_){
_start:
{
if (lean_obj_tag(v_x_1213_) == 0)
{
return v_x_1212_;
}
else
{
lean_object* v_key_1214_; lean_object* v_value_1215_; lean_object* v_tail_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1239_; 
v_key_1214_ = lean_ctor_get(v_x_1213_, 0);
v_value_1215_ = lean_ctor_get(v_x_1213_, 1);
v_tail_1216_ = lean_ctor_get(v_x_1213_, 2);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_x_1213_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1218_ = v_x_1213_;
v_isShared_1219_ = v_isSharedCheck_1239_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_tail_1216_);
lean_inc(v_value_1215_);
lean_inc(v_key_1214_);
lean_dec(v_x_1213_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1239_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; uint64_t v___x_1221_; uint64_t v___x_1222_; uint64_t v___x_1223_; uint64_t v_fold_1224_; uint64_t v___x_1225_; uint64_t v___x_1226_; uint64_t v___x_1227_; size_t v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1220_ = lean_array_get_size(v_x_1212_);
v___x_1221_ = lean_string_hash(v_key_1214_);
v___x_1222_ = 32ULL;
v___x_1223_ = lean_uint64_shift_right(v___x_1221_, v___x_1222_);
v_fold_1224_ = lean_uint64_xor(v___x_1221_, v___x_1223_);
v___x_1225_ = 16ULL;
v___x_1226_ = lean_uint64_shift_right(v_fold_1224_, v___x_1225_);
v___x_1227_ = lean_uint64_xor(v_fold_1224_, v___x_1226_);
v___x_1228_ = lean_uint64_to_usize(v___x_1227_);
v___x_1229_ = lean_usize_of_nat(v___x_1220_);
v___x_1230_ = ((size_t)1ULL);
v___x_1231_ = lean_usize_sub(v___x_1229_, v___x_1230_);
v___x_1232_ = lean_usize_land(v___x_1228_, v___x_1231_);
v___x_1233_ = lean_array_uget_borrowed(v_x_1212_, v___x_1232_);
lean_inc(v___x_1233_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 2, v___x_1233_);
v___x_1235_ = v___x_1218_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_key_1214_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_value_1215_);
lean_ctor_set(v_reuseFailAlloc_1238_, 2, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_array_uset(v_x_1212_, v___x_1232_, v___x_1235_);
v_x_1212_ = v___x_1236_;
v_x_1213_ = v_tail_1216_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1240_, lean_object* v_source_1241_, lean_object* v_target_1242_){
_start:
{
lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = lean_array_get_size(v_source_1241_);
v___x_1244_ = lean_nat_dec_lt(v_i_1240_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_dec_ref(v_source_1241_);
lean_dec(v_i_1240_);
return v_target_1242_;
}
else
{
lean_object* v_es_1245_; lean_object* v___x_1246_; lean_object* v_source_1247_; lean_object* v_target_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_es_1245_ = lean_array_fget(v_source_1241_, v_i_1240_);
v___x_1246_ = lean_box(0);
v_source_1247_ = lean_array_fset(v_source_1241_, v_i_1240_, v___x_1246_);
v_target_1248_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1242_, v_es_1245_);
v___x_1249_ = lean_unsigned_to_nat(1u);
v___x_1250_ = lean_nat_add(v_i_1240_, v___x_1249_);
lean_dec(v_i_1240_);
v_i_1240_ = v___x_1250_;
v_source_1241_ = v_source_1247_;
v_target_1242_ = v_target_1248_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(lean_object* v_data_1252_){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v_nbuckets_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1253_ = lean_array_get_size(v_data_1252_);
v___x_1254_ = lean_unsigned_to_nat(2u);
v_nbuckets_1255_ = lean_nat_mul(v___x_1253_, v___x_1254_);
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_box(0);
v___x_1258_ = lean_mk_array(v_nbuckets_1255_, v___x_1257_);
v___x_1259_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v___x_1256_, v_data_1252_, v___x_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(lean_object* v_i_1260_, lean_object* v_m_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_size_1263_; lean_object* v_buckets_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1314_; 
v_size_1263_ = lean_ctor_get(v_m_1261_, 0);
v_buckets_1264_ = lean_ctor_get(v_m_1261_, 1);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_m_1261_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1266_ = v_m_1261_;
v_isShared_1267_ = v_isSharedCheck_1314_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_buckets_1264_);
lean_inc(v_size_1263_);
lean_dec(v_m_1261_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1314_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; uint64_t v___x_1269_; uint64_t v___x_1270_; uint64_t v___x_1271_; uint64_t v_fold_1272_; uint64_t v___x_1273_; uint64_t v___x_1274_; uint64_t v___x_1275_; size_t v___x_1276_; size_t v___x_1277_; size_t v___x_1278_; size_t v___x_1279_; size_t v___x_1280_; lean_object* v_bkt_1281_; uint8_t v___x_1282_; 
v___x_1268_ = lean_array_get_size(v_buckets_1264_);
v___x_1269_ = lean_string_hash(v_a_1262_);
v___x_1270_ = 32ULL;
v___x_1271_ = lean_uint64_shift_right(v___x_1269_, v___x_1270_);
v_fold_1272_ = lean_uint64_xor(v___x_1269_, v___x_1271_);
v___x_1273_ = 16ULL;
v___x_1274_ = lean_uint64_shift_right(v_fold_1272_, v___x_1273_);
v___x_1275_ = lean_uint64_xor(v_fold_1272_, v___x_1274_);
v___x_1276_ = lean_uint64_to_usize(v___x_1275_);
v___x_1277_ = lean_usize_of_nat(v___x_1268_);
v___x_1278_ = ((size_t)1ULL);
v___x_1279_ = lean_usize_sub(v___x_1277_, v___x_1278_);
v___x_1280_ = lean_usize_land(v___x_1276_, v___x_1279_);
v_bkt_1281_ = lean_array_uget_borrowed(v_buckets_1264_, v___x_1280_);
v___x_1282_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1262_, v_bkt_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v_size_x27_1286_; lean_object* v___x_1287_; lean_object* v_buckets_x27_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1283_ = lean_unsigned_to_nat(1u);
v___x_1284_ = lean_mk_empty_array_with_capacity(v___x_1283_);
v___x_1285_ = lean_array_push(v___x_1284_, v_i_1260_);
v_size_x27_1286_ = lean_nat_add(v_size_1263_, v___x_1283_);
lean_dec(v_size_1263_);
lean_inc(v_bkt_1281_);
v___x_1287_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1287_, 0, v_a_1262_);
lean_ctor_set(v___x_1287_, 1, v___x_1285_);
lean_ctor_set(v___x_1287_, 2, v_bkt_1281_);
v_buckets_x27_1288_ = lean_array_uset(v_buckets_1264_, v___x_1280_, v___x_1287_);
v___x_1289_ = lean_unsigned_to_nat(4u);
v___x_1290_ = lean_nat_mul(v_size_x27_1286_, v___x_1289_);
v___x_1291_ = lean_unsigned_to_nat(3u);
v___x_1292_ = lean_nat_div(v___x_1290_, v___x_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_array_get_size(v_buckets_x27_1288_);
v___x_1294_ = lean_nat_dec_le(v___x_1292_, v___x_1293_);
lean_dec(v___x_1292_);
if (v___x_1294_ == 0)
{
lean_object* v_val_1295_; lean_object* v___x_1297_; 
v_val_1295_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_buckets_x27_1288_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v_val_1295_);
lean_ctor_set(v___x_1266_, 0, v_size_x27_1286_);
v___x_1297_ = v___x_1266_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_size_x27_1286_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_val_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
else
{
lean_object* v___x_1300_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v_buckets_x27_1288_);
lean_ctor_set(v___x_1266_, 0, v_size_x27_1286_);
v___x_1300_ = v___x_1266_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_size_x27_1286_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_buckets_x27_1288_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
else
{
lean_object* v___x_1302_; lean_object* v_buckets_x27_1303_; lean_object* v_bkt_x27_1304_; lean_object* v___y_1306_; uint8_t v___x_1311_; 
lean_inc(v_bkt_1281_);
v___x_1302_ = lean_box(0);
v_buckets_x27_1303_ = lean_array_uset(v_buckets_1264_, v___x_1280_, v___x_1302_);
lean_inc_ref(v_a_1262_);
v_bkt_x27_1304_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_1260_, v_a_1262_, v_bkt_1281_);
v___x_1311_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1262_, v_bkt_x27_1304_);
lean_dec_ref(v_a_1262_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_unsigned_to_nat(1u);
v___x_1313_ = lean_nat_sub(v_size_1263_, v___x_1312_);
lean_dec(v_size_1263_);
v___y_1306_ = v___x_1313_;
goto v___jp_1305_;
}
else
{
v___y_1306_ = v_size_1263_;
goto v___jp_1305_;
}
v___jp_1305_:
{
lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1307_ = lean_array_uset(v_buckets_x27_1303_, v___x_1280_, v_bkt_x27_1304_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v___x_1307_);
lean_ctor_set(v___x_1266_, 0, v___y_1306_);
v___x_1309_ = v___x_1266_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___y_1306_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header(lean_object* v_builder_1315_, lean_object* v_key_1316_, lean_object* v_value_1317_){
_start:
{
lean_object* v_line_1318_; lean_object* v_headers_1319_; lean_object* v_extensions_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1351_; 
v_line_1318_ = lean_ctor_get(v_builder_1315_, 0);
lean_inc_ref(v_line_1318_);
v_headers_1319_ = lean_ctor_get(v_line_1318_, 1);
lean_inc_ref(v_headers_1319_);
v_extensions_1320_ = lean_ctor_get(v_builder_1315_, 1);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_builder_1315_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; 
v_unused_1352_ = lean_ctor_get(v_builder_1315_, 0);
lean_dec(v_unused_1352_);
v___x_1322_ = v_builder_1315_;
v_isShared_1323_ = v_isSharedCheck_1351_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_extensions_1320_);
lean_dec(v_builder_1315_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1351_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
uint8_t v_method_1324_; uint8_t v_version_1325_; lean_object* v_uri_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1349_; 
v_method_1324_ = lean_ctor_get_uint8(v_line_1318_, sizeof(void*)*2);
v_version_1325_ = lean_ctor_get_uint8(v_line_1318_, sizeof(void*)*2 + 1);
v_uri_1326_ = lean_ctor_get(v_line_1318_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_line_1318_);
if (v_isSharedCheck_1349_ == 0)
{
lean_object* v_unused_1350_; 
v_unused_1350_ = lean_ctor_get(v_line_1318_, 1);
lean_dec(v_unused_1350_);
v___x_1328_ = v_line_1318_;
v_isShared_1329_ = v_isSharedCheck_1349_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_uri_1326_);
lean_dec(v_line_1318_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1349_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v_entries_1330_; lean_object* v_indexes_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1348_; 
v_entries_1330_ = lean_ctor_get(v_headers_1319_, 0);
v_indexes_1331_ = lean_ctor_get(v_headers_1319_, 1);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_headers_1319_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1333_ = v_headers_1319_;
v_isShared_1334_ = v_isSharedCheck_1348_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_indexes_1331_);
lean_inc(v_entries_1330_);
lean_dec(v_headers_1319_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1348_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v_i_1335_; lean_object* v___x_1336_; lean_object* v_entries_1337_; lean_object* v_indexes_1338_; lean_object* v___x_1340_; 
v_i_1335_ = lean_array_get_size(v_entries_1330_);
lean_inc_ref(v_key_1316_);
v___x_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1336_, 0, v_key_1316_);
lean_ctor_set(v___x_1336_, 1, v_value_1317_);
v_entries_1337_ = lean_array_push(v_entries_1330_, v___x_1336_);
v_indexes_1338_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1335_, v_indexes_1331_, v_key_1316_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 1, v_indexes_1338_);
lean_ctor_set(v___x_1333_, 0, v_entries_1337_);
v___x_1340_ = v___x_1333_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_entries_1337_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_indexes_1338_);
v___x_1340_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1342_; 
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 1, v___x_1340_);
v___x_1342_ = v___x_1328_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_uri_1326_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v___x_1340_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*2, v_method_1324_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*2 + 1, v_version_1325_);
v___x_1342_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1344_; 
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v___x_1342_);
v___x_1344_ = v___x_1322_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_extensions_1320_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(lean_object* v_00_u03b2_1353_, lean_object* v_a_1354_, lean_object* v_x_1355_){
_start:
{
uint8_t v___x_1356_; 
v___x_1356_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_1354_, v_x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1357_, lean_object* v_a_1358_, lean_object* v_x_1359_){
_start:
{
uint8_t v_res_1360_; lean_object* v_r_1361_; 
v_res_1360_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(v_00_u03b2_1357_, v_a_1358_, v_x_1359_);
lean_dec(v_x_1359_);
lean_dec_ref(v_a_1358_);
v_r_1361_ = lean_box(v_res_1360_);
return v_r_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1(lean_object* v_00_u03b2_1362_, lean_object* v_data_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_data_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1365_, lean_object* v_i_1366_, lean_object* v_source_1367_, lean_object* v_target_1368_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v_i_1366_, v_source_1367_, v_target_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1370_, lean_object* v_x_1371_, lean_object* v_x_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1371_, v_x_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x21(lean_object* v_builder_1374_, lean_object* v_key_1375_, lean_object* v_value_1376_){
_start:
{
lean_object* v_line_1377_; lean_object* v_headers_1378_; lean_object* v_extensions_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1412_; 
v_line_1377_ = lean_ctor_get(v_builder_1374_, 0);
lean_inc_ref(v_line_1377_);
v_headers_1378_ = lean_ctor_get(v_line_1377_, 1);
lean_inc_ref(v_headers_1378_);
v_extensions_1379_ = lean_ctor_get(v_builder_1374_, 1);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_builder_1374_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v_builder_1374_, 0);
lean_dec(v_unused_1413_);
v___x_1381_ = v_builder_1374_;
v_isShared_1382_ = v_isSharedCheck_1412_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_extensions_1379_);
lean_dec(v_builder_1374_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1412_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
uint8_t v_method_1383_; uint8_t v_version_1384_; lean_object* v_uri_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1410_; 
v_method_1383_ = lean_ctor_get_uint8(v_line_1377_, sizeof(void*)*2);
v_version_1384_ = lean_ctor_get_uint8(v_line_1377_, sizeof(void*)*2 + 1);
v_uri_1385_ = lean_ctor_get(v_line_1377_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_line_1377_);
if (v_isSharedCheck_1410_ == 0)
{
lean_object* v_unused_1411_; 
v_unused_1411_ = lean_ctor_get(v_line_1377_, 1);
lean_dec(v_unused_1411_);
v___x_1387_ = v_line_1377_;
v_isShared_1388_ = v_isSharedCheck_1410_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_uri_1385_);
lean_dec(v_line_1377_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1410_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v_entries_1389_; lean_object* v_indexes_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1409_; 
v_entries_1389_ = lean_ctor_get(v_headers_1378_, 0);
v_indexes_1390_ = lean_ctor_get(v_headers_1378_, 1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_headers_1378_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1392_ = v_headers_1378_;
v_isShared_1393_ = v_isSharedCheck_1409_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_indexes_1390_);
lean_inc(v_entries_1389_);
lean_dec(v_headers_1378_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1409_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_key_1394_; lean_object* v_value_1395_; lean_object* v_i_1396_; lean_object* v___x_1397_; lean_object* v_entries_1398_; lean_object* v_indexes_1399_; lean_object* v___x_1401_; 
v_key_1394_ = l_Std_Http_Header_Name_ofString_x21(v_key_1375_);
v_value_1395_ = l_Std_Http_Header_Value_ofString_x21(v_value_1376_);
v_i_1396_ = lean_array_get_size(v_entries_1389_);
lean_inc_ref(v_key_1394_);
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v_key_1394_);
lean_ctor_set(v___x_1397_, 1, v_value_1395_);
v_entries_1398_ = lean_array_push(v_entries_1389_, v___x_1397_);
v_indexes_1399_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1396_, v_indexes_1390_, v_key_1394_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 1, v_indexes_1399_);
lean_ctor_set(v___x_1392_, 0, v_entries_1398_);
v___x_1401_ = v___x_1392_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_entries_1398_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_indexes_1399_);
v___x_1401_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1403_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v___x_1401_);
v___x_1403_ = v___x_1387_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_uri_1385_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v___x_1401_);
lean_ctor_set_uint8(v_reuseFailAlloc_1407_, sizeof(void*)*2, v_method_1383_);
lean_ctor_set_uint8(v_reuseFailAlloc_1407_, sizeof(void*)*2 + 1, v_version_1384_);
v___x_1403_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1405_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1403_);
v___x_1405_ = v___x_1381_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_extensions_1379_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x3f(lean_object* v_builder_1414_, lean_object* v_key_1415_, lean_object* v_value_1416_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Std_Http_Header_Name_ofString_x3f(v_key_1415_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v___x_1418_; 
lean_dec_ref(v_value_1416_);
lean_dec_ref(v_builder_1414_);
v___x_1418_ = lean_box(0);
return v___x_1418_;
}
else
{
lean_object* v_val_1419_; lean_object* v___x_1420_; 
v_val_1419_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_val_1419_);
lean_dec_ref(v___x_1417_);
v___x_1420_ = l_Std_Http_Header_Value_ofString_x3f(v_value_1416_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v___x_1421_; 
lean_dec(v_val_1419_);
lean_dec_ref(v_builder_1414_);
v___x_1421_ = lean_box(0);
return v___x_1421_;
}
else
{
lean_object* v_line_1422_; lean_object* v_headers_1423_; lean_object* v_val_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1464_; 
v_line_1422_ = lean_ctor_get(v_builder_1414_, 0);
lean_inc_ref(v_line_1422_);
v_headers_1423_ = lean_ctor_get(v_line_1422_, 1);
lean_inc_ref(v_headers_1423_);
v_val_1424_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1426_ = v___x_1420_;
v_isShared_1427_ = v_isSharedCheck_1464_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_val_1424_);
lean_dec(v___x_1420_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1464_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v_extensions_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1462_; 
v_extensions_1428_ = lean_ctor_get(v_builder_1414_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_builder_1414_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v_builder_1414_, 0);
lean_dec(v_unused_1463_);
v___x_1430_ = v_builder_1414_;
v_isShared_1431_ = v_isSharedCheck_1462_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_extensions_1428_);
lean_dec(v_builder_1414_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1462_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
uint8_t v_method_1432_; uint8_t v_version_1433_; lean_object* v_uri_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1460_; 
v_method_1432_ = lean_ctor_get_uint8(v_line_1422_, sizeof(void*)*2);
v_version_1433_ = lean_ctor_get_uint8(v_line_1422_, sizeof(void*)*2 + 1);
v_uri_1434_ = lean_ctor_get(v_line_1422_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_line_1422_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v_line_1422_, 1);
lean_dec(v_unused_1461_);
v___x_1436_ = v_line_1422_;
v_isShared_1437_ = v_isSharedCheck_1460_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_uri_1434_);
lean_dec(v_line_1422_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1460_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_entries_1438_; lean_object* v_indexes_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1459_; 
v_entries_1438_ = lean_ctor_get(v_headers_1423_, 0);
v_indexes_1439_ = lean_ctor_get(v_headers_1423_, 1);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_headers_1423_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1441_ = v_headers_1423_;
v_isShared_1442_ = v_isSharedCheck_1459_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_indexes_1439_);
lean_inc(v_entries_1438_);
lean_dec(v_headers_1423_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1459_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v_i_1443_; lean_object* v___x_1444_; lean_object* v_entries_1445_; lean_object* v_indexes_1446_; lean_object* v___x_1448_; 
v_i_1443_ = lean_array_get_size(v_entries_1438_);
lean_inc(v_val_1419_);
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v_val_1419_);
lean_ctor_set(v___x_1444_, 1, v_val_1424_);
v_entries_1445_ = lean_array_push(v_entries_1438_, v___x_1444_);
v_indexes_1446_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_1443_, v_indexes_1439_, v_val_1419_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 1, v_indexes_1446_);
lean_ctor_set(v___x_1441_, 0, v_entries_1445_);
v___x_1448_ = v___x_1441_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_entries_1445_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_indexes_1446_);
v___x_1448_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1450_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v___x_1448_);
v___x_1450_ = v___x_1436_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_uri_1434_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v___x_1448_);
lean_ctor_set_uint8(v_reuseFailAlloc_1457_, sizeof(void*)*2, v_method_1432_);
lean_ctor_set_uint8(v_reuseFailAlloc_1457_, sizeof(void*)*2 + 1, v_version_1433_);
v___x_1450_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1450_);
v___x_1452_ = v___x_1430_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_extensions_1428_);
v___x_1452_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1454_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1452_);
v___x_1454_ = v___x_1426_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
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
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headerOpt(lean_object* v_builder_1465_, lean_object* v_key_1466_, lean_object* v_value_1467_){
_start:
{
if (lean_obj_tag(v_value_1467_) == 0)
{
lean_dec_ref(v_key_1466_);
return v_builder_1465_;
}
else
{
lean_object* v_val_1468_; lean_object* v___x_1469_; 
v_val_1468_ = lean_ctor_get(v_value_1467_, 0);
lean_inc(v_val_1468_);
lean_dec_ref(v_value_1467_);
v___x_1469_ = l_Std_Http_Request_Builder_header(v_builder_1465_, v_key_1466_, v_val_1468_);
return v___x_1469_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension___redArg(lean_object* v_builder_1471_, lean_object* v_inst_1472_, lean_object* v_data_1473_){
_start:
{
lean_object* v_line_1474_; lean_object* v_extensions_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1486_; 
v_line_1474_ = lean_ctor_get(v_builder_1471_, 0);
v_extensions_1475_ = lean_ctor_get(v_builder_1471_, 1);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_builder_1471_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1477_ = v_builder_1471_;
v_isShared_1478_ = v_isSharedCheck_1486_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_extensions_1475_);
lean_inc(v_line_1474_);
lean_dec(v_builder_1471_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1486_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v_dyn_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
v_dyn_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_1479_, 0, v_inst_1472_);
lean_ctor_set(v_dyn_1479_, 1, v_data_1473_);
v___x_1480_ = ((lean_object*)(l_Std_Http_Request_Builder_extension___redArg___closed__0));
v___x_1481_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_1479_);
v___x_1482_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_1480_, v___x_1481_, v_dyn_1479_, v_extensions_1475_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 1, v___x_1482_);
v___x_1484_ = v___x_1477_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_line_1474_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension(lean_object* v_00_u03b1_1487_, lean_object* v_builder_1488_, lean_object* v_inst_1489_, lean_object* v_data_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Std_Http_Request_Builder_extension___redArg(v_builder_1488_, v_inst_1489_, v_data_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object* v_builder_1492_, lean_object* v_body_1493_){
_start:
{
lean_object* v_line_1494_; lean_object* v_extensions_1495_; lean_object* v___x_1496_; 
v_line_1494_ = lean_ctor_get(v_builder_1492_, 0);
v_extensions_1495_ = lean_ctor_get(v_builder_1492_, 1);
lean_inc(v_extensions_1495_);
lean_inc_ref(v_line_1494_);
v___x_1496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1496_, 0, v_line_1494_);
lean_ctor_set(v___x_1496_, 1, v_body_1493_);
lean_ctor_set(v___x_1496_, 2, v_extensions_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg___boxed(lean_object* v_builder_1497_, lean_object* v_body_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1497_, v_body_1498_);
lean_dec_ref(v_builder_1497_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body(lean_object* v_t_1500_, lean_object* v_builder_1501_, lean_object* v_body_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1501_, v_body_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___boxed(lean_object* v_t_1504_, lean_object* v_builder_1505_, lean_object* v_body_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Std_Http_Request_Builder_body(v_t_1504_, v_builder_1505_, v_body_1506_);
lean_dec_ref(v_builder_1505_);
return v_res_1507_;
}
}
static lean_object* _init_l_Std_Http_Request_get___closed__0(void){
_start:
{
uint8_t v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1508_ = 8;
v___x_1509_ = l_Std_Http_Request_new;
v___x_1510_ = l_Std_Http_Request_Builder_method(v___x_1509_, v___x_1508_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_get(lean_object* v_uri_1511_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_obj_once(&l_Std_Http_Request_get___closed__0, &l_Std_Http_Request_get___closed__0_once, _init_l_Std_Http_Request_get___closed__0);
v___x_1513_ = l_Std_Http_Request_Builder_uri(v___x_1512_, v_uri_1511_);
return v___x_1513_;
}
}
static lean_object* _init_l_Std_Http_Request_post___closed__0(void){
_start:
{
uint8_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1514_ = 23;
v___x_1515_ = l_Std_Http_Request_new;
v___x_1516_ = l_Std_Http_Request_Builder_method(v___x_1515_, v___x_1514_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_post(lean_object* v_uri_1517_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_obj_once(&l_Std_Http_Request_post___closed__0, &l_Std_Http_Request_post___closed__0_once, _init_l_Std_Http_Request_post___closed__0);
v___x_1519_ = l_Std_Http_Request_Builder_uri(v___x_1518_, v_uri_1517_);
return v___x_1519_;
}
}
static lean_object* _init_l_Std_Http_Request_put___closed__0(void){
_start:
{
uint8_t v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = 27;
v___x_1521_ = l_Std_Http_Request_new;
v___x_1522_ = l_Std_Http_Request_Builder_method(v___x_1521_, v___x_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_put(lean_object* v_uri_1523_){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_obj_once(&l_Std_Http_Request_put___closed__0, &l_Std_Http_Request_put___closed__0_once, _init_l_Std_Http_Request_put___closed__0);
v___x_1525_ = l_Std_Http_Request_Builder_uri(v___x_1524_, v_uri_1523_);
return v___x_1525_;
}
}
static lean_object* _init_l_Std_Http_Request_delete___closed__0(void){
_start:
{
uint8_t v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1526_ = 7;
v___x_1527_ = l_Std_Http_Request_new;
v___x_1528_ = l_Std_Http_Request_Builder_method(v___x_1527_, v___x_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_delete(lean_object* v_uri_1529_){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = lean_obj_once(&l_Std_Http_Request_delete___closed__0, &l_Std_Http_Request_delete___closed__0_once, _init_l_Std_Http_Request_delete___closed__0);
v___x_1531_ = l_Std_Http_Request_Builder_uri(v___x_1530_, v_uri_1529_);
return v___x_1531_;
}
}
static lean_object* _init_l_Std_Http_Request_patch___closed__0(void){
_start:
{
uint8_t v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1532_ = 22;
v___x_1533_ = l_Std_Http_Request_new;
v___x_1534_ = l_Std_Http_Request_Builder_method(v___x_1533_, v___x_1532_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_patch(lean_object* v_uri_1535_){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_obj_once(&l_Std_Http_Request_patch___closed__0, &l_Std_Http_Request_patch___closed__0_once, _init_l_Std_Http_Request_patch___closed__0);
v___x_1537_ = l_Std_Http_Request_Builder_uri(v___x_1536_, v_uri_1535_);
return v___x_1537_;
}
}
static lean_object* _init_l_Std_Http_Request_head___closed__0(void){
_start:
{
uint8_t v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = 9;
v___x_1539_ = l_Std_Http_Request_new;
v___x_1540_ = l_Std_Http_Request_Builder_method(v___x_1539_, v___x_1538_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_head(lean_object* v_uri_1541_){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_obj_once(&l_Std_Http_Request_head___closed__0, &l_Std_Http_Request_head___closed__0_once, _init_l_Std_Http_Request_head___closed__0);
v___x_1543_ = l_Std_Http_Request_Builder_uri(v___x_1542_, v_uri_1541_);
return v___x_1543_;
}
}
static lean_object* _init_l_Std_Http_Request_options___closed__0(void){
_start:
{
uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = 20;
v___x_1545_ = l_Std_Http_Request_new;
v___x_1546_ = l_Std_Http_Request_Builder_method(v___x_1545_, v___x_1544_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_options(lean_object* v_uri_1547_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_obj_once(&l_Std_Http_Request_options___closed__0, &l_Std_Http_Request_options___closed__0_once, _init_l_Std_Http_Request_options___closed__0);
v___x_1549_ = l_Std_Http_Request_Builder_uri(v___x_1548_, v_uri_1547_);
return v___x_1549_;
}
}
static lean_object* _init_l_Std_Http_Request_connect___closed__0(void){
_start:
{
uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = 5;
v___x_1551_ = l_Std_Http_Request_new;
v___x_1552_ = l_Std_Http_Request_Builder_method(v___x_1551_, v___x_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_connect(lean_object* v_uri_1553_){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_obj_once(&l_Std_Http_Request_connect___closed__0, &l_Std_Http_Request_connect___closed__0_once, _init_l_Std_Http_Request_connect___closed__0);
v___x_1555_ = l_Std_Http_Request_Builder_uri(v___x_1554_, v_uri_1553_);
return v___x_1555_;
}
}
static lean_object* _init_l_Std_Http_Request_trace___closed__0(void){
_start:
{
uint8_t v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = 32;
v___x_1557_ = l_Std_Http_Request_new;
v___x_1558_ = l_Std_Http_Request_Builder_method(v___x_1557_, v___x_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_trace(lean_object* v_uri_1559_){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_obj_once(&l_Std_Http_Request_trace___closed__0, &l_Std_Http_Request_trace___closed__0_once, _init_l_Std_Http_Request_trace___closed__0);
v___x_1561_ = l_Std_Http_Request_Builder_uri(v___x_1560_, v_uri_1559_);
return v___x_1561_;
}
}
lean_object* runtime_initialize_Std_Internal_Http_Data_Extensions(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Method(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Version(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Headers(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_URI(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Data_Request(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Http_Data_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Method(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_URI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Request_instInhabitedHead_default = _init_l_Std_Http_Request_instInhabitedHead_default();
lean_mark_persistent(l_Std_Http_Request_instInhabitedHead_default);
l_Std_Http_Request_instInhabitedHead = _init_l_Std_Http_Request_instInhabitedHead();
lean_mark_persistent(l_Std_Http_Request_instInhabitedHead);
l_Std_Http_Request_new = _init_l_Std_Http_Request_new();
lean_mark_persistent(l_Std_Http_Request_new);
l_Std_Http_Request_Builder_empty = _init_l_Std_Http_Request_Builder_empty();
lean_mark_persistent(l_Std_Http_Request_Builder_empty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Data_Request(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Http_Data_Extensions(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Method(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Version(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Headers(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_URI(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Data_Request(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Http_Data_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Method(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_URI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Data_Request(builtin);
}
#ifdef __cplusplus
}
#endif
