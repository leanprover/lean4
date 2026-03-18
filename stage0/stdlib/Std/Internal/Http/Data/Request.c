// Lean compiler output
// Module: Std.Internal.Http.Data.Request
// Imports: public import Std.Internal.Http.Data.Extensions public import Std.Internal.Http.Data.Method public import Std.Internal.Http.Data.Version public import Std.Internal.Http.Data.Headers
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Extensions_empty;
extern lean_object* l_Std_Http_Headers_empty;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_instInhabitedHeaders_default;
extern lean_object* l_Std_Http_instInhabitedExtensions_default;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Http_instReprMethod_repr(uint8_t, lean_object*);
lean_object* l_Std_Http_instReprVersion_repr(uint8_t, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Http_Header_Name_ofString_x21(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* l_Std_Http_Extensions_compareName___boxed(lean_object*, lean_object*);
lean_object* l_Std_Http_Header_Name_ofString_x3f(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x3f(lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Request_instInhabitedHead_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Request_instInhabitedHead_default___closed__0 = (const lean_object*)&l_Std_Http_Request_instInhabitedHead_default___closed__0_value;
static lean_once_cell_t l_Std_Http_Request_instInhabitedHead_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instInhabitedHead_default___closed__1;
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
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__1___closed__0 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__1___closed__0_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__1___closed__1 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__1___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__11 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__11_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.0"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__12 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__12_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.1"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__13 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__13_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/2.0"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__14 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__14_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/3.0"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__15 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__15_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ACL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__16 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__16_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BASELINE-CONTROL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__17 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__17_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "BIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__18 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__18_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CHECKIN"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__19 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__19_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CHECKOUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__20 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__20_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CONNECT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__21 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__21_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COPY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__22 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__22_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DELETE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__23 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__23_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__24 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__24_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__25 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__25_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "LABEL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__26 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__26_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LINK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__27 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__27_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LOCK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__28 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__28_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MERGE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__29 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__29_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKACTIVITY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__30 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__30_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKCALENDAR"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__31 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__31_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MKCOL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__32 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__32_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MKREDIRECTREF"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__33 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__33_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MKWORKSPACE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__34 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__34_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MOVE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__35 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__35_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__36 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__36_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ORDERPATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__37 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__37_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__38 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__38_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__39 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__39_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRI"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__40 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__40_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PROPFIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__41 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__41_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PROPPATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__42 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__42_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__43 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__43_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "QUERY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__44 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__44_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REBIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__45 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__45_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REPORT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__46 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__46_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SEARCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__47 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__47_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TRACE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__48 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__48_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNBIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__49 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__49_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UNCHECKOUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__50 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__50_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLINK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__51 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__51_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLOCK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__52 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__52_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UPDATE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__53 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__53_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UPDATEREDIRECTREF"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__54 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__54_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__2___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "VERSION-CONTROL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__2___closed__55 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__2___closed__55_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__0 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value)} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__1 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__1_value;
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__2, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___closed__1_value)} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__2 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Http_Request_instToStringHead = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Request_instEncodeV11Head___lam__0___closed__2;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3;
static lean_once_cell_t l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Request_instEncodeV11Head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instEncodeV11Head___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value)} };
static const lean_object* l_Std_Http_Request_instEncodeV11Head___closed__0 = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__0_value;
static const lean_closure_object l_Std_Http_Request_instEncodeV11Head___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instEncodeV11Head___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__0_value)} };
static const lean_object* l_Std_Http_Request_instEncodeV11Head___closed__1 = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Request_instEncodeV11Head = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__1_value;
static const lean_string_object l_Std_Http_Request_new___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Std_Http_Request_new___closed__0 = (const lean_object*)&l_Std_Http_Request_new___closed__0_value;
static lean_once_cell_t l_Std_Http_Request_new___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_new___closed__1;
static lean_once_cell_t l_Std_Http_Request_new___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_new___closed__2;
LEAN_EXPORT lean_object* l_Std_Http_Request_new;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_empty;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri(lean_object*, lean_object*);
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
static lean_object* _init_l_Std_Http_Request_instInhabitedHead_default___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; uint8_t v___x_4_; uint8_t v___x_5_; lean_object* v___x_6_; 
v___x_2_ = l_Std_Http_instInhabitedHeaders_default;
v___x_3_ = ((lean_object*)(l_Std_Http_Request_instInhabitedHead_default___closed__0));
v___x_4_ = 0;
v___x_5_ = 0;
v___x_6_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_6_, 0, v___x_3_);
lean_ctor_set(v___x_6_, 1, v___x_2_);
lean_ctor_set_uint8(v___x_6_, sizeof(void*)*2, v___x_5_);
lean_ctor_set_uint8(v___x_6_, sizeof(void*)*2 + 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Std_Http_Request_instInhabitedHead_default(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&l_Std_Http_Request_instInhabitedHead_default___closed__1, &l_Std_Http_Request_instInhabitedHead_default___closed__1_once, _init_l_Std_Http_Request_instInhabitedHead_default___closed__1);
return v___x_7_;
}
}
static lean_object* _init_l_Std_Http_Request_instInhabitedHead(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Std_Http_Request_instInhabitedHead_default;
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Request_instReprHead_repr_spec__0(lean_object* v_a_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_nat_to_int(v_a_9_);
return v___x_10_;
}
}
static lean_object* _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_unsigned_to_nat(10u);
v___x_25_ = lean_nat_to_int(v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_unsigned_to_nat(11u);
v___x_33_ = lean_nat_to_int(v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_unsigned_to_nat(7u);
v___x_38_ = lean_nat_to_int(v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__0));
v___x_44_ = lean_string_length(v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_obj_once(&l_Std_Http_Request_instReprHead_repr___redArg___closed__19, &l_Std_Http_Request_instReprHead_repr___redArg___closed__19_once, _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__19);
v___x_46_ = lean_nat_to_int(v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instReprHead_repr___redArg(lean_object* v_x_51_){
_start:
{
uint8_t v_method_52_; uint8_t v_version_53_; lean_object* v_uri_54_; lean_object* v_headers_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_method_52_ = lean_ctor_get_uint8(v_x_51_, sizeof(void*)*2);
v_version_53_ = lean_ctor_get_uint8(v_x_51_, sizeof(void*)*2 + 1);
v_uri_54_ = lean_ctor_get(v_x_51_, 0);
lean_inc_ref(v_uri_54_);
v_headers_55_ = lean_ctor_get(v_x_51_, 1);
lean_inc_ref(v_headers_55_);
lean_dec_ref(v_x_51_);
v___x_56_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__5));
v___x_57_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__6));
v___x_58_ = lean_obj_once(&l_Std_Http_Request_instReprHead_repr___redArg___closed__7, &l_Std_Http_Request_instReprHead_repr___redArg___closed__7_once, _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__7);
v___x_59_ = lean_unsigned_to_nat(0u);
v___x_60_ = l_Std_Http_instReprMethod_repr(v_method_52_, v___x_59_);
v___x_61_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_58_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = 0;
v___x_63_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_63_, 0, v___x_61_);
lean_ctor_set_uint8(v___x_63_, sizeof(void*)*1, v___x_62_);
v___x_64_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_57_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
v___x_65_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__9));
v___x_66_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_64_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = lean_box(1);
v___x_68_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_66_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__11));
v___x_70_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_68_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
v___x_71_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_56_);
v___x_72_ = lean_obj_once(&l_Std_Http_Request_instReprHead_repr___redArg___closed__12, &l_Std_Http_Request_instReprHead_repr___redArg___closed__12_once, _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__12);
v___x_73_ = l_Std_Http_instReprVersion_repr(v_version_53_, v___x_59_);
v___x_74_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_72_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set_uint8(v___x_75_, sizeof(void*)*1, v___x_62_);
v___x_76_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_71_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___x_65_);
v___x_78_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_67_);
v___x_79_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__14));
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_56_);
v___x_82_ = lean_obj_once(&l_Std_Http_Request_instReprHead_repr___redArg___closed__15, &l_Std_Http_Request_instReprHead_repr___redArg___closed__15_once, _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__15);
v___x_83_ = l_String_quote(v_uri_54_);
v___x_84_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
v___x_85_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_82_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_62_);
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_81_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_65_);
v___x_89_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v___x_67_);
v___x_90_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__17));
v___x_91_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set(v___x_92_, 1, v___x_56_);
v___x_93_ = l_Std_Http_instReprHeaders_repr___redArg(v_headers_55_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_72_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*1, v___x_62_);
v___x_96_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_92_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = lean_obj_once(&l_Std_Http_Request_instReprHead_repr___redArg___closed__20, &l_Std_Http_Request_instReprHead_repr___redArg___closed__20_once, _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__20);
v___x_98_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__21));
v___x_99_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_96_);
v___x_100_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__22));
v___x_101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_99_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_97_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*1, v___x_62_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instReprHead_repr(lean_object* v_x_104_, lean_object* v_prec_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instReprHead_repr___boxed(lean_object* v_x_107_, lean_object* v_prec_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Std_Http_Request_instReprHead_repr(v_x_107_, v_prec_108_);
lean_dec(v_prec_108_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest_default___redArg(lean_object* v_inst_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = l_Std_Http_Request_instInhabitedHead_default;
v___x_114_ = l_Std_Http_instInhabitedExtensions_default;
v___x_115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set(v___x_115_, 1, v_inst_112_);
lean_ctor_set(v___x_115_, 2, v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest_default(lean_object* v_a_116_, lean_object* v_inst_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Std_Http_instInhabitedRequest_default___redArg(v_inst_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest___redArg(lean_object* v_inst_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Std_Http_instInhabitedRequest_default___redArg(v_inst_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest(lean_object* v_a_121_, lean_object* v_inst_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Std_Http_instInhabitedRequest_default___redArg(v_inst_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__0(lean_object* v_x_124_){
_start:
{
lean_object* v___x_125_; uint32_t v___x_126_; uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_string_utf8_get(v_x_124_, v___x_125_);
v___x_127_ = 97;
v___x_128_ = lean_uint32_dec_le(v___x_127_, v___x_126_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_string_utf8_set(v_x_124_, v___x_125_, v___x_126_);
return v___x_129_;
}
else
{
uint32_t v___x_130_; uint8_t v___x_131_; 
v___x_130_ = 122;
v___x_131_ = lean_uint32_dec_le(v___x_126_, v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; 
v___x_132_ = lean_string_utf8_set(v_x_124_, v___x_125_, v___x_126_);
return v___x_132_;
}
else
{
uint32_t v___x_133_; uint32_t v___x_134_; lean_object* v___x_135_; 
v___x_133_ = 4294967264;
v___x_134_ = lean_uint32_add(v___x_126_, v___x_133_);
v___x_135_ = lean_string_utf8_set(v_x_124_, v___x_125_, v___x_134_);
return v___x_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__1(lean_object* v___f_138_, lean_object* v_x_139_){
_start:
{
lean_object* v_fst_140_; lean_object* v_snd_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v_it_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_fst_140_ = lean_ctor_get(v_x_139_, 0);
v_snd_141_ = lean_ctor_get(v_x_139_, 1);
v___x_142_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__0));
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = lean_box(0);
v___x_145_ = l_String_splitOnAux(v_fst_140_, v___x_142_, v___x_143_, v___x_143_, v___x_143_, v___x_144_);
v_it_146_ = l_List_mapTR_loop___redArg(v___f_138_, v___x_145_, v___x_144_);
v___x_147_ = l_String_intercalate(v___x_142_, v_it_146_);
v___x_148_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__1));
v___x_149_ = lean_string_append(v___x_147_, v___x_148_);
v___x_150_ = lean_string_append(v___x_149_, v_snd_141_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__1___boxed(lean_object* v___f_151_, lean_object* v_x_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Std_Http_Request_instToStringHead___lam__1(v___f_151_, v_x_152_);
lean_dec_ref(v_x_152_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__2(lean_object* v___f_219_, lean_object* v_req_220_){
_start:
{
lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; uint8_t v_method_237_; uint8_t v_version_238_; lean_object* v_uri_239_; lean_object* v_headers_240_; lean_object* v___y_242_; 
v_method_237_ = lean_ctor_get_uint8(v_req_220_, sizeof(void*)*2);
v_version_238_ = lean_ctor_get_uint8(v_req_220_, sizeof(void*)*2 + 1);
v_uri_239_ = lean_ctor_get(v_req_220_, 0);
lean_inc_ref(v_uri_239_);
v_headers_240_ = lean_ctor_get(v_req_220_, 1);
lean_inc_ref(v_headers_240_);
lean_dec_ref(v_req_220_);
switch(v_method_237_)
{
case 0:
{
lean_object* v___x_251_; 
v___x_251_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__16));
v___y_242_ = v___x_251_;
goto v___jp_241_;
}
case 1:
{
lean_object* v___x_252_; 
v___x_252_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__17));
v___y_242_ = v___x_252_;
goto v___jp_241_;
}
case 2:
{
lean_object* v___x_253_; 
v___x_253_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__18));
v___y_242_ = v___x_253_;
goto v___jp_241_;
}
case 3:
{
lean_object* v___x_254_; 
v___x_254_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__19));
v___y_242_ = v___x_254_;
goto v___jp_241_;
}
case 4:
{
lean_object* v___x_255_; 
v___x_255_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__20));
v___y_242_ = v___x_255_;
goto v___jp_241_;
}
case 5:
{
lean_object* v___x_256_; 
v___x_256_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__21));
v___y_242_ = v___x_256_;
goto v___jp_241_;
}
case 6:
{
lean_object* v___x_257_; 
v___x_257_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__22));
v___y_242_ = v___x_257_;
goto v___jp_241_;
}
case 7:
{
lean_object* v___x_258_; 
v___x_258_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__23));
v___y_242_ = v___x_258_;
goto v___jp_241_;
}
case 8:
{
lean_object* v___x_259_; 
v___x_259_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__24));
v___y_242_ = v___x_259_;
goto v___jp_241_;
}
case 9:
{
lean_object* v___x_260_; 
v___x_260_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__25));
v___y_242_ = v___x_260_;
goto v___jp_241_;
}
case 10:
{
lean_object* v___x_261_; 
v___x_261_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__26));
v___y_242_ = v___x_261_;
goto v___jp_241_;
}
case 11:
{
lean_object* v___x_262_; 
v___x_262_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__27));
v___y_242_ = v___x_262_;
goto v___jp_241_;
}
case 12:
{
lean_object* v___x_263_; 
v___x_263_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__28));
v___y_242_ = v___x_263_;
goto v___jp_241_;
}
case 13:
{
lean_object* v___x_264_; 
v___x_264_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__29));
v___y_242_ = v___x_264_;
goto v___jp_241_;
}
case 14:
{
lean_object* v___x_265_; 
v___x_265_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__30));
v___y_242_ = v___x_265_;
goto v___jp_241_;
}
case 15:
{
lean_object* v___x_266_; 
v___x_266_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__31));
v___y_242_ = v___x_266_;
goto v___jp_241_;
}
case 16:
{
lean_object* v___x_267_; 
v___x_267_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__32));
v___y_242_ = v___x_267_;
goto v___jp_241_;
}
case 17:
{
lean_object* v___x_268_; 
v___x_268_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__33));
v___y_242_ = v___x_268_;
goto v___jp_241_;
}
case 18:
{
lean_object* v___x_269_; 
v___x_269_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__34));
v___y_242_ = v___x_269_;
goto v___jp_241_;
}
case 19:
{
lean_object* v___x_270_; 
v___x_270_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__35));
v___y_242_ = v___x_270_;
goto v___jp_241_;
}
case 20:
{
lean_object* v___x_271_; 
v___x_271_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__36));
v___y_242_ = v___x_271_;
goto v___jp_241_;
}
case 21:
{
lean_object* v___x_272_; 
v___x_272_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__37));
v___y_242_ = v___x_272_;
goto v___jp_241_;
}
case 22:
{
lean_object* v___x_273_; 
v___x_273_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__38));
v___y_242_ = v___x_273_;
goto v___jp_241_;
}
case 23:
{
lean_object* v___x_274_; 
v___x_274_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__39));
v___y_242_ = v___x_274_;
goto v___jp_241_;
}
case 24:
{
lean_object* v___x_275_; 
v___x_275_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__40));
v___y_242_ = v___x_275_;
goto v___jp_241_;
}
case 25:
{
lean_object* v___x_276_; 
v___x_276_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__41));
v___y_242_ = v___x_276_;
goto v___jp_241_;
}
case 26:
{
lean_object* v___x_277_; 
v___x_277_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__42));
v___y_242_ = v___x_277_;
goto v___jp_241_;
}
case 27:
{
lean_object* v___x_278_; 
v___x_278_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__43));
v___y_242_ = v___x_278_;
goto v___jp_241_;
}
case 28:
{
lean_object* v___x_279_; 
v___x_279_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__44));
v___y_242_ = v___x_279_;
goto v___jp_241_;
}
case 29:
{
lean_object* v___x_280_; 
v___x_280_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__45));
v___y_242_ = v___x_280_;
goto v___jp_241_;
}
case 30:
{
lean_object* v___x_281_; 
v___x_281_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__46));
v___y_242_ = v___x_281_;
goto v___jp_241_;
}
case 31:
{
lean_object* v___x_282_; 
v___x_282_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__47));
v___y_242_ = v___x_282_;
goto v___jp_241_;
}
case 32:
{
lean_object* v___x_283_; 
v___x_283_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__48));
v___y_242_ = v___x_283_;
goto v___jp_241_;
}
case 33:
{
lean_object* v___x_284_; 
v___x_284_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__49));
v___y_242_ = v___x_284_;
goto v___jp_241_;
}
case 34:
{
lean_object* v___x_285_; 
v___x_285_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__50));
v___y_242_ = v___x_285_;
goto v___jp_241_;
}
case 35:
{
lean_object* v___x_286_; 
v___x_286_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__51));
v___y_242_ = v___x_286_;
goto v___jp_241_;
}
case 36:
{
lean_object* v___x_287_; 
v___x_287_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__52));
v___y_242_ = v___x_287_;
goto v___jp_241_;
}
case 37:
{
lean_object* v___x_288_; 
v___x_288_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__53));
v___y_242_ = v___x_288_;
goto v___jp_241_;
}
case 38:
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__54));
v___y_242_ = v___x_289_;
goto v___jp_241_;
}
default: 
{
lean_object* v___x_290_; 
v___x_290_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__55));
v___y_242_ = v___x_290_;
goto v___jp_241_;
}
}
v___jp_221_:
{
lean_object* v_entries_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; size_t v_sz_230_; size_t v___x_231_; lean_object* v_pairs_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_entries_225_ = lean_ctor_get(v___y_223_, 0);
lean_inc_ref(v_entries_225_);
lean_dec_ref(v___y_223_);
v___x_226_ = lean_string_append(v___y_222_, v___y_224_);
lean_dec_ref(v___y_224_);
v___x_227_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__0));
v___x_228_ = lean_string_append(v___x_226_, v___x_227_);
v___x_229_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__10));
v_sz_230_ = lean_array_size(v_entries_225_);
v___x_231_ = ((size_t)0ULL);
v_pairs_232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_229_, v___f_219_, v_sz_230_, v___x_231_, v_entries_225_);
v___x_233_ = lean_array_to_list(v_pairs_232_);
v___x_234_ = l_String_intercalate(v___x_227_, v___x_233_);
v___x_235_ = lean_string_append(v___x_228_, v___x_234_);
lean_dec_ref(v___x_234_);
v___x_236_ = lean_string_append(v___x_235_, v___x_227_);
return v___x_236_;
}
v___jp_241_:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_243_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__11));
v___x_244_ = lean_string_append(v___y_242_, v___x_243_);
v___x_245_ = lean_string_append(v___x_244_, v_uri_239_);
lean_dec_ref(v_uri_239_);
v___x_246_ = lean_string_append(v___x_245_, v___x_243_);
switch(v_version_238_)
{
case 0:
{
lean_object* v___x_247_; 
v___x_247_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__12));
v___y_222_ = v___x_246_;
v___y_223_ = v_headers_240_;
v___y_224_ = v___x_247_;
goto v___jp_221_;
}
case 1:
{
lean_object* v___x_248_; 
v___x_248_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__13));
v___y_222_ = v___x_246_;
v___y_223_ = v_headers_240_;
v___y_224_ = v___x_248_;
goto v___jp_221_;
}
case 2:
{
lean_object* v___x_249_; 
v___x_249_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__14));
v___y_222_ = v___x_246_;
v___y_223_ = v_headers_240_;
v___y_224_ = v___x_249_;
goto v___jp_221_;
}
default: 
{
lean_object* v___x_250_; 
v___x_250_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___y_222_ = v___x_246_;
v___y_223_ = v_headers_240_;
v___y_224_ = v___x_250_;
goto v___jp_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1(lean_object* v___f_297_, lean_object* v_buf_298_, lean_object* v_name_299_, lean_object* v_value_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_data_305_; lean_object* v_size_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_324_; 
v___x_301_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__0));
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_box(0);
v___x_304_ = l_String_splitOnAux(v_name_299_, v___x_301_, v___x_302_, v___x_302_, v___x_302_, v___x_303_);
v_data_305_ = lean_ctor_get(v_buf_298_, 0);
v_size_306_ = lean_ctor_get(v_buf_298_, 1);
v_isSharedCheck_324_ = !lean_is_exclusive(v_buf_298_);
if (v_isSharedCheck_324_ == 0)
{
v___x_308_ = v_buf_298_;
v_isShared_309_ = v_isSharedCheck_324_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_size_306_);
lean_inc(v_data_305_);
lean_dec(v_buf_298_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_324_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_it_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v_it_310_ = l_List_mapTR_loop___redArg(v___f_297_, v___x_304_, v___x_303_);
v___x_311_ = l_String_intercalate(v___x_301_, v_it_310_);
v___x_312_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__1___closed__1));
v___x_313_ = lean_string_append(v___x_311_, v___x_312_);
v___x_314_ = lean_string_append(v___x_313_, v_value_300_);
v___x_315_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__0));
v___x_316_ = lean_string_append(v___x_314_, v___x_315_);
v___x_317_ = lean_string_to_utf8(v___x_316_);
lean_dec_ref(v___x_316_);
lean_inc_ref(v___x_317_);
v___x_318_ = lean_array_push(v_data_305_, v___x_317_);
v___x_319_ = lean_byte_array_size(v___x_317_);
lean_dec_ref(v___x_317_);
v___x_320_ = lean_nat_add(v_size_306_, v___x_319_);
lean_dec(v_size_306_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_320_);
lean_ctor_set(v___x_308_, 0, v___x_318_);
v___x_322_ = v___x_308_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__1___boxed(lean_object* v___f_325_, lean_object* v_buf_326_, lean_object* v_name_327_, lean_object* v_value_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Std_Http_Request_instEncodeV11Head___lam__1(v___f_325_, v_buf_326_, v_name_327_, v_value_328_);
lean_dec_ref(v_value_328_);
lean_dec_ref(v_name_327_);
return v_res_329_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__0));
v___x_331_ = lean_string_to_utf8(v___x_330_);
return v___x_331_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0);
v___x_333_ = lean_byte_array_size(v___x_332_);
return v___x_333_;
}
}
static uint8_t _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__2(void){
_start:
{
uint32_t v___x_334_; uint8_t v___x_335_; 
v___x_334_ = 32;
v___x_335_ = lean_uint32_to_uint8(v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3(void){
_start:
{
uint8_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_336_ = lean_uint8_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__2, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__2_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__2);
v___x_337_ = lean_unsigned_to_nat(1u);
v___x_338_ = lean_mk_empty_array_with_capacity(v___x_337_);
v___x_339_ = lean_box(v___x_336_);
v___x_340_ = lean_array_push(v___x_338_, v___x_339_);
v___x_341_ = lean_byte_array_mk(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3);
v___x_343_ = lean_byte_array_size(v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0(lean_object* v___f_344_, lean_object* v_buffer_345_, lean_object* v_req_346_){
_start:
{
lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; uint8_t v_method_373_; uint8_t v_version_374_; lean_object* v_uri_375_; lean_object* v_headers_376_; lean_object* v___y_378_; 
v_method_373_ = lean_ctor_get_uint8(v_req_346_, sizeof(void*)*2);
v_version_374_ = lean_ctor_get_uint8(v_req_346_, sizeof(void*)*2 + 1);
v_uri_375_ = lean_ctor_get(v_req_346_, 0);
v_headers_376_ = lean_ctor_get(v_req_346_, 1);
switch(v_method_373_)
{
case 0:
{
lean_object* v___x_399_; 
v___x_399_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__16));
v___y_378_ = v___x_399_;
goto v___jp_377_;
}
case 1:
{
lean_object* v___x_400_; 
v___x_400_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__17));
v___y_378_ = v___x_400_;
goto v___jp_377_;
}
case 2:
{
lean_object* v___x_401_; 
v___x_401_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__18));
v___y_378_ = v___x_401_;
goto v___jp_377_;
}
case 3:
{
lean_object* v___x_402_; 
v___x_402_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__19));
v___y_378_ = v___x_402_;
goto v___jp_377_;
}
case 4:
{
lean_object* v___x_403_; 
v___x_403_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__20));
v___y_378_ = v___x_403_;
goto v___jp_377_;
}
case 5:
{
lean_object* v___x_404_; 
v___x_404_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__21));
v___y_378_ = v___x_404_;
goto v___jp_377_;
}
case 6:
{
lean_object* v___x_405_; 
v___x_405_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__22));
v___y_378_ = v___x_405_;
goto v___jp_377_;
}
case 7:
{
lean_object* v___x_406_; 
v___x_406_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__23));
v___y_378_ = v___x_406_;
goto v___jp_377_;
}
case 8:
{
lean_object* v___x_407_; 
v___x_407_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__24));
v___y_378_ = v___x_407_;
goto v___jp_377_;
}
case 9:
{
lean_object* v___x_408_; 
v___x_408_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__25));
v___y_378_ = v___x_408_;
goto v___jp_377_;
}
case 10:
{
lean_object* v___x_409_; 
v___x_409_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__26));
v___y_378_ = v___x_409_;
goto v___jp_377_;
}
case 11:
{
lean_object* v___x_410_; 
v___x_410_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__27));
v___y_378_ = v___x_410_;
goto v___jp_377_;
}
case 12:
{
lean_object* v___x_411_; 
v___x_411_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__28));
v___y_378_ = v___x_411_;
goto v___jp_377_;
}
case 13:
{
lean_object* v___x_412_; 
v___x_412_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__29));
v___y_378_ = v___x_412_;
goto v___jp_377_;
}
case 14:
{
lean_object* v___x_413_; 
v___x_413_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__30));
v___y_378_ = v___x_413_;
goto v___jp_377_;
}
case 15:
{
lean_object* v___x_414_; 
v___x_414_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__31));
v___y_378_ = v___x_414_;
goto v___jp_377_;
}
case 16:
{
lean_object* v___x_415_; 
v___x_415_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__32));
v___y_378_ = v___x_415_;
goto v___jp_377_;
}
case 17:
{
lean_object* v___x_416_; 
v___x_416_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__33));
v___y_378_ = v___x_416_;
goto v___jp_377_;
}
case 18:
{
lean_object* v___x_417_; 
v___x_417_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__34));
v___y_378_ = v___x_417_;
goto v___jp_377_;
}
case 19:
{
lean_object* v___x_418_; 
v___x_418_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__35));
v___y_378_ = v___x_418_;
goto v___jp_377_;
}
case 20:
{
lean_object* v___x_419_; 
v___x_419_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__36));
v___y_378_ = v___x_419_;
goto v___jp_377_;
}
case 21:
{
lean_object* v___x_420_; 
v___x_420_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__37));
v___y_378_ = v___x_420_;
goto v___jp_377_;
}
case 22:
{
lean_object* v___x_421_; 
v___x_421_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__38));
v___y_378_ = v___x_421_;
goto v___jp_377_;
}
case 23:
{
lean_object* v___x_422_; 
v___x_422_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__39));
v___y_378_ = v___x_422_;
goto v___jp_377_;
}
case 24:
{
lean_object* v___x_423_; 
v___x_423_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__40));
v___y_378_ = v___x_423_;
goto v___jp_377_;
}
case 25:
{
lean_object* v___x_424_; 
v___x_424_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__41));
v___y_378_ = v___x_424_;
goto v___jp_377_;
}
case 26:
{
lean_object* v___x_425_; 
v___x_425_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__42));
v___y_378_ = v___x_425_;
goto v___jp_377_;
}
case 27:
{
lean_object* v___x_426_; 
v___x_426_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__43));
v___y_378_ = v___x_426_;
goto v___jp_377_;
}
case 28:
{
lean_object* v___x_427_; 
v___x_427_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__44));
v___y_378_ = v___x_427_;
goto v___jp_377_;
}
case 29:
{
lean_object* v___x_428_; 
v___x_428_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__45));
v___y_378_ = v___x_428_;
goto v___jp_377_;
}
case 30:
{
lean_object* v___x_429_; 
v___x_429_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__46));
v___y_378_ = v___x_429_;
goto v___jp_377_;
}
case 31:
{
lean_object* v___x_430_; 
v___x_430_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__47));
v___y_378_ = v___x_430_;
goto v___jp_377_;
}
case 32:
{
lean_object* v___x_431_; 
v___x_431_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__48));
v___y_378_ = v___x_431_;
goto v___jp_377_;
}
case 33:
{
lean_object* v___x_432_; 
v___x_432_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__49));
v___y_378_ = v___x_432_;
goto v___jp_377_;
}
case 34:
{
lean_object* v___x_433_; 
v___x_433_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__50));
v___y_378_ = v___x_433_;
goto v___jp_377_;
}
case 35:
{
lean_object* v___x_434_; 
v___x_434_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__51));
v___y_378_ = v___x_434_;
goto v___jp_377_;
}
case 36:
{
lean_object* v___x_435_; 
v___x_435_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__52));
v___y_378_ = v___x_435_;
goto v___jp_377_;
}
case 37:
{
lean_object* v___x_436_; 
v___x_436_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__53));
v___y_378_ = v___x_436_;
goto v___jp_377_;
}
case 38:
{
lean_object* v___x_437_; 
v___x_437_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__54));
v___y_378_ = v___x_437_;
goto v___jp_377_;
}
default: 
{
lean_object* v___x_438_; 
v___x_438_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__55));
v___y_378_ = v___x_438_;
goto v___jp_377_;
}
}
v___jp_347_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v_buffer_360_; lean_object* v_buffer_361_; lean_object* v_data_362_; lean_object* v_size_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_372_; 
v___x_352_ = lean_string_to_utf8(v___y_351_);
lean_dec_ref(v___y_351_);
lean_inc_ref(v___x_352_);
v___x_353_ = lean_array_push(v___y_349_, v___x_352_);
v___x_354_ = lean_byte_array_size(v___x_352_);
lean_dec_ref(v___x_352_);
v___x_355_ = lean_nat_add(v___y_348_, v___x_354_);
lean_dec(v___y_348_);
v___x_356_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0);
v___x_357_ = lean_array_push(v___x_353_, v___x_356_);
v___x_358_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1);
v___x_359_ = lean_nat_add(v___x_355_, v___x_358_);
lean_dec(v___x_355_);
v_buffer_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_buffer_360_, 0, v___x_357_);
lean_ctor_set(v_buffer_360_, 1, v___x_359_);
v_buffer_361_ = l_Std_Http_Headers_fold___redArg(v___y_350_, v_buffer_360_, v___f_344_);
v_data_362_ = lean_ctor_get(v_buffer_361_, 0);
v_size_363_ = lean_ctor_get(v_buffer_361_, 1);
v_isSharedCheck_372_ = !lean_is_exclusive(v_buffer_361_);
if (v_isSharedCheck_372_ == 0)
{
v___x_365_ = v_buffer_361_;
v_isShared_366_ = v_isSharedCheck_372_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_size_363_);
lean_inc(v_data_362_);
lean_dec(v_buffer_361_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_372_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_367_ = lean_array_push(v_data_362_, v___x_356_);
v___x_368_ = lean_nat_add(v_size_363_, v___x_358_);
lean_dec(v_size_363_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 1, v___x_368_);
lean_ctor_set(v___x_365_, 0, v___x_367_);
v___x_370_ = v___x_365_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
v___jp_377_:
{
lean_object* v_data_379_; lean_object* v_size_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_data_379_ = lean_ctor_get(v_buffer_345_, 0);
lean_inc_ref(v_data_379_);
v_size_380_ = lean_ctor_get(v_buffer_345_, 1);
lean_inc(v_size_380_);
lean_dec_ref(v_buffer_345_);
v___x_381_ = lean_string_to_utf8(v___y_378_);
lean_dec_ref(v___y_378_);
lean_inc_ref(v___x_381_);
v___x_382_ = lean_array_push(v_data_379_, v___x_381_);
v___x_383_ = lean_byte_array_size(v___x_381_);
lean_dec_ref(v___x_381_);
v___x_384_ = lean_nat_add(v_size_380_, v___x_383_);
lean_dec(v_size_380_);
v___x_385_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3);
v___x_386_ = lean_array_push(v___x_382_, v___x_385_);
v___x_387_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4);
v___x_388_ = lean_nat_add(v___x_384_, v___x_387_);
lean_dec(v___x_384_);
v___x_389_ = lean_string_to_utf8(v_uri_375_);
lean_inc_ref(v___x_389_);
v___x_390_ = lean_array_push(v___x_386_, v___x_389_);
v___x_391_ = lean_byte_array_size(v___x_389_);
lean_dec_ref(v___x_389_);
v___x_392_ = lean_nat_add(v___x_388_, v___x_391_);
lean_dec(v___x_388_);
v___x_393_ = lean_array_push(v___x_390_, v___x_385_);
v___x_394_ = lean_nat_add(v___x_392_, v___x_387_);
lean_dec(v___x_392_);
switch(v_version_374_)
{
case 0:
{
lean_object* v___x_395_; 
v___x_395_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__12));
v___y_348_ = v___x_394_;
v___y_349_ = v___x_393_;
v___y_350_ = v_headers_376_;
v___y_351_ = v___x_395_;
goto v___jp_347_;
}
case 1:
{
lean_object* v___x_396_; 
v___x_396_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__13));
v___y_348_ = v___x_394_;
v___y_349_ = v___x_393_;
v___y_350_ = v_headers_376_;
v___y_351_ = v___x_396_;
goto v___jp_347_;
}
case 2:
{
lean_object* v___x_397_; 
v___x_397_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__14));
v___y_348_ = v___x_394_;
v___y_349_ = v___x_393_;
v___y_350_ = v_headers_376_;
v___y_351_ = v___x_397_;
goto v___jp_347_;
}
default: 
{
lean_object* v___x_398_; 
v___x_398_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__2___closed__15));
v___y_348_ = v___x_394_;
v___y_349_ = v___x_393_;
v___y_350_ = v_headers_376_;
v___y_351_ = v___x_398_;
goto v___jp_347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___boxed(lean_object* v___f_439_, lean_object* v_buffer_440_, lean_object* v_req_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Std_Http_Request_instEncodeV11Head___lam__0(v___f_439_, v_buffer_440_, v_req_441_);
lean_dec_ref(v_req_441_);
return v_res_442_;
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__1(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; uint8_t v___x_452_; lean_object* v___x_453_; 
v___x_449_ = l_Std_Http_Headers_empty;
v___x_450_ = ((lean_object*)(l_Std_Http_Request_new___closed__0));
v___x_451_ = 1;
v___x_452_ = 8;
v___x_453_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_453_, 0, v___x_450_);
lean_ctor_set(v___x_453_, 1, v___x_449_);
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*2, v___x_452_);
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*2 + 1, v___x_451_);
return v___x_453_;
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__2(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = l_Std_Http_Extensions_empty;
v___x_455_ = lean_obj_once(&l_Std_Http_Request_new___closed__1, &l_Std_Http_Request_new___closed__1_once, _init_l_Std_Http_Request_new___closed__1);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l_Std_Http_Request_new(void){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lean_obj_once(&l_Std_Http_Request_new___closed__2, &l_Std_Http_Request_new___closed__2_once, _init_l_Std_Http_Request_new___closed__2);
return v___x_457_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_empty(void){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = lean_obj_once(&l_Std_Http_Request_new___closed__2, &l_Std_Http_Request_new___closed__2_once, _init_l_Std_Http_Request_new___closed__2);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method(lean_object* v_builder_459_, uint8_t v_method_460_){
_start:
{
lean_object* v_line_461_; lean_object* v_extensions_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_479_; 
v_line_461_ = lean_ctor_get(v_builder_459_, 0);
v_extensions_462_ = lean_ctor_get(v_builder_459_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_builder_459_);
if (v_isSharedCheck_479_ == 0)
{
v___x_464_ = v_builder_459_;
v_isShared_465_ = v_isSharedCheck_479_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_extensions_462_);
lean_inc(v_line_461_);
lean_dec(v_builder_459_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_479_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v_version_466_; lean_object* v_uri_467_; lean_object* v_headers_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_478_; 
v_version_466_ = lean_ctor_get_uint8(v_line_461_, sizeof(void*)*2 + 1);
v_uri_467_ = lean_ctor_get(v_line_461_, 0);
v_headers_468_ = lean_ctor_get(v_line_461_, 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v_line_461_);
if (v_isSharedCheck_478_ == 0)
{
v___x_470_ = v_line_461_;
v_isShared_471_ = v_isSharedCheck_478_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_headers_468_);
lean_inc(v_uri_467_);
lean_dec(v_line_461_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_478_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_uri_467_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_headers_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_477_, sizeof(void*)*2 + 1, v_version_466_);
v___x_473_ = v_reuseFailAlloc_477_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_475_; 
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*2, v_method_460_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_473_);
v___x_475_ = v___x_464_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_extensions_462_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method___boxed(lean_object* v_builder_480_, lean_object* v_method_481_){
_start:
{
uint8_t v_method_boxed_482_; lean_object* v_res_483_; 
v_method_boxed_482_ = lean_unbox(v_method_481_);
v_res_483_ = l_Std_Http_Request_Builder_method(v_builder_480_, v_method_boxed_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version(lean_object* v_builder_484_, uint8_t v_version_485_){
_start:
{
lean_object* v_line_486_; lean_object* v_extensions_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_504_; 
v_line_486_ = lean_ctor_get(v_builder_484_, 0);
v_extensions_487_ = lean_ctor_get(v_builder_484_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v_builder_484_);
if (v_isSharedCheck_504_ == 0)
{
v___x_489_ = v_builder_484_;
v_isShared_490_ = v_isSharedCheck_504_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_extensions_487_);
lean_inc(v_line_486_);
lean_dec(v_builder_484_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_504_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
uint8_t v_method_491_; lean_object* v_uri_492_; lean_object* v_headers_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_503_; 
v_method_491_ = lean_ctor_get_uint8(v_line_486_, sizeof(void*)*2);
v_uri_492_ = lean_ctor_get(v_line_486_, 0);
v_headers_493_ = lean_ctor_get(v_line_486_, 1);
v_isSharedCheck_503_ = !lean_is_exclusive(v_line_486_);
if (v_isSharedCheck_503_ == 0)
{
v___x_495_ = v_line_486_;
v_isShared_496_ = v_isSharedCheck_503_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_headers_493_);
lean_inc(v_uri_492_);
lean_dec(v_line_486_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_503_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_uri_492_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_headers_493_);
lean_ctor_set_uint8(v_reuseFailAlloc_502_, sizeof(void*)*2, v_method_491_);
v___x_498_ = v_reuseFailAlloc_502_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_500_; 
lean_ctor_set_uint8(v___x_498_, sizeof(void*)*2 + 1, v_version_485_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_498_);
v___x_500_ = v___x_489_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_extensions_487_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version___boxed(lean_object* v_builder_505_, lean_object* v_version_506_){
_start:
{
uint8_t v_version_boxed_507_; lean_object* v_res_508_; 
v_version_boxed_507_ = lean_unbox(v_version_506_);
v_res_508_ = l_Std_Http_Request_Builder_version(v_builder_505_, v_version_boxed_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri(lean_object* v_builder_509_, lean_object* v_uri_510_){
_start:
{
lean_object* v_line_511_; lean_object* v_extensions_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_530_; 
v_line_511_ = lean_ctor_get(v_builder_509_, 0);
v_extensions_512_ = lean_ctor_get(v_builder_509_, 1);
v_isSharedCheck_530_ = !lean_is_exclusive(v_builder_509_);
if (v_isSharedCheck_530_ == 0)
{
v___x_514_ = v_builder_509_;
v_isShared_515_ = v_isSharedCheck_530_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_extensions_512_);
lean_inc(v_line_511_);
lean_dec(v_builder_509_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_530_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
uint8_t v_method_516_; uint8_t v_version_517_; lean_object* v_headers_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_528_; 
v_method_516_ = lean_ctor_get_uint8(v_line_511_, sizeof(void*)*2);
v_version_517_ = lean_ctor_get_uint8(v_line_511_, sizeof(void*)*2 + 1);
v_headers_518_ = lean_ctor_get(v_line_511_, 1);
v_isSharedCheck_528_ = !lean_is_exclusive(v_line_511_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v_line_511_, 0);
lean_dec(v_unused_529_);
v___x_520_ = v_line_511_;
v_isShared_521_ = v_isSharedCheck_528_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_headers_518_);
lean_dec(v_line_511_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_528_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v_uri_510_);
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_uri_510_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_headers_518_);
lean_ctor_set_uint8(v_reuseFailAlloc_527_, sizeof(void*)*2, v_method_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_527_, sizeof(void*)*2 + 1, v_version_517_);
v___x_523_ = v_reuseFailAlloc_527_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_525_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_523_);
v___x_525_ = v___x_514_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_extensions_512_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headers(lean_object* v_builder_531_, lean_object* v_headers_532_){
_start:
{
lean_object* v_line_533_; lean_object* v_extensions_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_552_; 
v_line_533_ = lean_ctor_get(v_builder_531_, 0);
v_extensions_534_ = lean_ctor_get(v_builder_531_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_builder_531_);
if (v_isSharedCheck_552_ == 0)
{
v___x_536_ = v_builder_531_;
v_isShared_537_ = v_isSharedCheck_552_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_extensions_534_);
lean_inc(v_line_533_);
lean_dec(v_builder_531_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_552_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
uint8_t v_method_538_; uint8_t v_version_539_; lean_object* v_uri_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_550_; 
v_method_538_ = lean_ctor_get_uint8(v_line_533_, sizeof(void*)*2);
v_version_539_ = lean_ctor_get_uint8(v_line_533_, sizeof(void*)*2 + 1);
v_uri_540_ = lean_ctor_get(v_line_533_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_line_533_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v_line_533_, 1);
lean_dec(v_unused_551_);
v___x_542_ = v_line_533_;
v_isShared_543_ = v_isSharedCheck_550_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_uri_540_);
lean_dec(v_line_533_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_550_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v_headers_532_);
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_uri_540_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_headers_532_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, sizeof(void*)*2, v_method_538_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, sizeof(void*)*2 + 1, v_version_539_);
v___x_545_ = v_reuseFailAlloc_549_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_547_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_545_);
v___x_547_ = v___x_536_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_extensions_534_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(lean_object* v_i_553_, lean_object* v_x_554_){
_start:
{
if (lean_obj_tag(v_x_554_) == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = lean_mk_empty_array_with_capacity(v___x_555_);
v___x_557_ = lean_array_push(v___x_556_, v_i_553_);
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
else
{
lean_object* v_val_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
v_val_559_ = lean_ctor_get(v_x_554_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v_x_554_);
if (v_isSharedCheck_567_ == 0)
{
v___x_561_ = v_x_554_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_val_559_);
lean_dec(v_x_554_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = lean_array_push(v_val_559_, v_i_553_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(lean_object* v_i_568_, lean_object* v_a_569_, lean_object* v_x_570_){
_start:
{
if (lean_obj_tag(v_x_570_) == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v_val_573_; lean_object* v___x_574_; 
v___x_571_ = lean_box(0);
v___x_572_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(v_i_568_, v___x_571_);
v_val_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_val_573_);
lean_dec(v___x_572_);
v___x_574_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_574_, 0, v_a_569_);
lean_ctor_set(v___x_574_, 1, v_val_573_);
lean_ctor_set(v___x_574_, 2, v_x_570_);
return v___x_574_;
}
else
{
lean_object* v_key_575_; lean_object* v_value_576_; lean_object* v_tail_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_592_; 
v_key_575_ = lean_ctor_get(v_x_570_, 0);
v_value_576_ = lean_ctor_get(v_x_570_, 1);
v_tail_577_ = lean_ctor_get(v_x_570_, 2);
v_isSharedCheck_592_ = !lean_is_exclusive(v_x_570_);
if (v_isSharedCheck_592_ == 0)
{
v___x_579_ = v_x_570_;
v_isShared_580_ = v_isSharedCheck_592_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_tail_577_);
lean_inc(v_value_576_);
lean_inc(v_key_575_);
lean_dec(v_x_570_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_592_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
uint8_t v___x_581_; 
v___x_581_ = lean_string_dec_eq(v_key_575_, v_a_569_);
if (v___x_581_ == 0)
{
lean_object* v_tail_582_; lean_object* v___x_584_; 
v_tail_582_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_568_, v_a_569_, v_tail_577_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 2, v_tail_582_);
v___x_584_ = v___x_579_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_key_575_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_value_576_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_tail_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_val_588_; lean_object* v___x_590_; 
lean_dec(v_key_575_);
v___x_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_586_, 0, v_value_576_);
v___x_587_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2___lam__0(v_i_568_, v___x_586_);
v_val_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_val_588_);
lean_dec(v___x_587_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 1, v_val_588_);
lean_ctor_set(v___x_579_, 0, v_a_569_);
v___x_590_ = v___x_579_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_569_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_val_588_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_tail_577_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(lean_object* v_a_593_, lean_object* v_x_594_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
uint8_t v___x_595_; 
v___x_595_ = 0;
return v___x_595_;
}
else
{
lean_object* v_key_596_; lean_object* v_tail_597_; uint8_t v___x_598_; 
v_key_596_ = lean_ctor_get(v_x_594_, 0);
v_tail_597_ = lean_ctor_get(v_x_594_, 2);
v___x_598_ = lean_string_dec_eq(v_key_596_, v_a_593_);
if (v___x_598_ == 0)
{
v_x_594_ = v_tail_597_;
goto _start;
}
else
{
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg___boxed(lean_object* v_a_600_, lean_object* v_x_601_){
_start:
{
uint8_t v_res_602_; lean_object* v_r_603_; 
v_res_602_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_600_, v_x_601_);
lean_dec(v_x_601_);
lean_dec_ref(v_a_600_);
v_r_603_ = lean_box(v_res_602_);
return v_r_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
if (lean_obj_tag(v_x_605_) == 0)
{
return v_x_604_;
}
else
{
lean_object* v_key_606_; lean_object* v_value_607_; lean_object* v_tail_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_631_; 
v_key_606_ = lean_ctor_get(v_x_605_, 0);
v_value_607_ = lean_ctor_get(v_x_605_, 1);
v_tail_608_ = lean_ctor_get(v_x_605_, 2);
v_isSharedCheck_631_ = !lean_is_exclusive(v_x_605_);
if (v_isSharedCheck_631_ == 0)
{
v___x_610_ = v_x_605_;
v_isShared_611_ = v_isSharedCheck_631_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_tail_608_);
lean_inc(v_value_607_);
lean_inc(v_key_606_);
lean_dec(v_x_605_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_631_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; uint64_t v___x_613_; uint64_t v___x_614_; uint64_t v___x_615_; uint64_t v_fold_616_; uint64_t v___x_617_; uint64_t v___x_618_; uint64_t v___x_619_; size_t v___x_620_; size_t v___x_621_; size_t v___x_622_; size_t v___x_623_; size_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_612_ = lean_array_get_size(v_x_604_);
v___x_613_ = lean_string_hash(v_key_606_);
v___x_614_ = 32ULL;
v___x_615_ = lean_uint64_shift_right(v___x_613_, v___x_614_);
v_fold_616_ = lean_uint64_xor(v___x_613_, v___x_615_);
v___x_617_ = 16ULL;
v___x_618_ = lean_uint64_shift_right(v_fold_616_, v___x_617_);
v___x_619_ = lean_uint64_xor(v_fold_616_, v___x_618_);
v___x_620_ = lean_uint64_to_usize(v___x_619_);
v___x_621_ = lean_usize_of_nat(v___x_612_);
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_sub(v___x_621_, v___x_622_);
v___x_624_ = lean_usize_land(v___x_620_, v___x_623_);
v___x_625_ = lean_array_uget_borrowed(v_x_604_, v___x_624_);
lean_inc(v___x_625_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 2, v___x_625_);
v___x_627_ = v___x_610_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_key_606_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_value_607_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v___x_625_);
v___x_627_ = v_reuseFailAlloc_630_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; 
v___x_628_ = lean_array_uset(v_x_604_, v___x_624_, v___x_627_);
v_x_604_ = v___x_628_;
v_x_605_ = v_tail_608_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(lean_object* v_i_632_, lean_object* v_source_633_, lean_object* v_target_634_){
_start:
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = lean_array_get_size(v_source_633_);
v___x_636_ = lean_nat_dec_lt(v_i_632_, v___x_635_);
if (v___x_636_ == 0)
{
lean_dec_ref(v_source_633_);
lean_dec(v_i_632_);
return v_target_634_;
}
else
{
lean_object* v_es_637_; lean_object* v___x_638_; lean_object* v_source_639_; lean_object* v_target_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_es_637_ = lean_array_fget(v_source_633_, v_i_632_);
v___x_638_ = lean_box(0);
v_source_639_ = lean_array_fset(v_source_633_, v_i_632_, v___x_638_);
v_target_640_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_target_634_, v_es_637_);
v___x_641_ = lean_unsigned_to_nat(1u);
v___x_642_ = lean_nat_add(v_i_632_, v___x_641_);
lean_dec(v_i_632_);
v_i_632_ = v___x_642_;
v_source_633_ = v_source_639_;
v_target_634_ = v_target_640_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(lean_object* v_data_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v_nbuckets_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_645_ = lean_array_get_size(v_data_644_);
v___x_646_ = lean_unsigned_to_nat(2u);
v_nbuckets_647_ = lean_nat_mul(v___x_645_, v___x_646_);
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = lean_box(0);
v___x_650_ = lean_mk_array(v_nbuckets_647_, v___x_649_);
v___x_651_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v___x_648_, v_data_644_, v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(lean_object* v_i_652_, lean_object* v_m_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_size_655_; lean_object* v_buckets_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_706_; 
v_size_655_ = lean_ctor_get(v_m_653_, 0);
v_buckets_656_ = lean_ctor_get(v_m_653_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v_m_653_);
if (v_isSharedCheck_706_ == 0)
{
v___x_658_ = v_m_653_;
v_isShared_659_ = v_isSharedCheck_706_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_buckets_656_);
lean_inc(v_size_655_);
lean_dec(v_m_653_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_706_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; uint64_t v___x_661_; uint64_t v___x_662_; uint64_t v___x_663_; uint64_t v_fold_664_; uint64_t v___x_665_; uint64_t v___x_666_; uint64_t v___x_667_; size_t v___x_668_; size_t v___x_669_; size_t v___x_670_; size_t v___x_671_; size_t v___x_672_; lean_object* v_bkt_673_; uint8_t v___x_674_; 
v___x_660_ = lean_array_get_size(v_buckets_656_);
v___x_661_ = lean_string_hash(v_a_654_);
v___x_662_ = 32ULL;
v___x_663_ = lean_uint64_shift_right(v___x_661_, v___x_662_);
v_fold_664_ = lean_uint64_xor(v___x_661_, v___x_663_);
v___x_665_ = 16ULL;
v___x_666_ = lean_uint64_shift_right(v_fold_664_, v___x_665_);
v___x_667_ = lean_uint64_xor(v_fold_664_, v___x_666_);
v___x_668_ = lean_uint64_to_usize(v___x_667_);
v___x_669_ = lean_usize_of_nat(v___x_660_);
v___x_670_ = ((size_t)1ULL);
v___x_671_ = lean_usize_sub(v___x_669_, v___x_670_);
v___x_672_ = lean_usize_land(v___x_668_, v___x_671_);
v_bkt_673_ = lean_array_uget_borrowed(v_buckets_656_, v___x_672_);
v___x_674_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_654_, v_bkt_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v_size_x27_678_; lean_object* v___x_679_; lean_object* v_buckets_x27_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_675_ = lean_unsigned_to_nat(1u);
v___x_676_ = lean_mk_empty_array_with_capacity(v___x_675_);
v___x_677_ = lean_array_push(v___x_676_, v_i_652_);
v_size_x27_678_ = lean_nat_add(v_size_655_, v___x_675_);
lean_dec(v_size_655_);
lean_inc(v_bkt_673_);
v___x_679_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_679_, 0, v_a_654_);
lean_ctor_set(v___x_679_, 1, v___x_677_);
lean_ctor_set(v___x_679_, 2, v_bkt_673_);
v_buckets_x27_680_ = lean_array_uset(v_buckets_656_, v___x_672_, v___x_679_);
v___x_681_ = lean_unsigned_to_nat(4u);
v___x_682_ = lean_nat_mul(v_size_x27_678_, v___x_681_);
v___x_683_ = lean_unsigned_to_nat(3u);
v___x_684_ = lean_nat_div(v___x_682_, v___x_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_array_get_size(v_buckets_x27_680_);
v___x_686_ = lean_nat_dec_le(v___x_684_, v___x_685_);
lean_dec(v___x_684_);
if (v___x_686_ == 0)
{
lean_object* v_val_687_; lean_object* v___x_689_; 
v_val_687_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_buckets_x27_680_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v_val_687_);
lean_ctor_set(v___x_658_, 0, v_size_x27_678_);
v___x_689_ = v___x_658_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_size_x27_678_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_val_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
else
{
lean_object* v___x_692_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v_buckets_x27_680_);
lean_ctor_set(v___x_658_, 0, v_size_x27_678_);
v___x_692_ = v___x_658_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_size_x27_678_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_buckets_x27_680_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
else
{
lean_object* v___x_694_; lean_object* v_buckets_x27_695_; lean_object* v_bkt_x27_696_; lean_object* v___y_698_; uint8_t v___x_703_; 
lean_inc(v_bkt_673_);
v___x_694_ = lean_box(0);
v_buckets_x27_695_ = lean_array_uset(v_buckets_656_, v___x_672_, v___x_694_);
lean_inc_ref(v_a_654_);
v_bkt_x27_696_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__2(v_i_652_, v_a_654_, v_bkt_673_);
v___x_703_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_654_, v_bkt_x27_696_);
lean_dec_ref(v_a_654_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_nat_sub(v_size_655_, v___x_704_);
lean_dec(v_size_655_);
v___y_698_ = v___x_705_;
goto v___jp_697_;
}
else
{
v___y_698_ = v_size_655_;
goto v___jp_697_;
}
v___jp_697_:
{
lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_699_ = lean_array_uset(v_buckets_x27_695_, v___x_672_, v_bkt_x27_696_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_699_);
lean_ctor_set(v___x_658_, 0, v___y_698_);
v___x_701_ = v___x_658_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___y_698_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header(lean_object* v_builder_707_, lean_object* v_key_708_, lean_object* v_value_709_){
_start:
{
lean_object* v_line_710_; lean_object* v_headers_711_; lean_object* v_extensions_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_743_; 
v_line_710_ = lean_ctor_get(v_builder_707_, 0);
lean_inc_ref(v_line_710_);
v_headers_711_ = lean_ctor_get(v_line_710_, 1);
lean_inc_ref(v_headers_711_);
v_extensions_712_ = lean_ctor_get(v_builder_707_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v_builder_707_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; 
v_unused_744_ = lean_ctor_get(v_builder_707_, 0);
lean_dec(v_unused_744_);
v___x_714_ = v_builder_707_;
v_isShared_715_ = v_isSharedCheck_743_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_extensions_712_);
lean_dec(v_builder_707_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_743_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
uint8_t v_method_716_; uint8_t v_version_717_; lean_object* v_uri_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_741_; 
v_method_716_ = lean_ctor_get_uint8(v_line_710_, sizeof(void*)*2);
v_version_717_ = lean_ctor_get_uint8(v_line_710_, sizeof(void*)*2 + 1);
v_uri_718_ = lean_ctor_get(v_line_710_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v_line_710_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v_line_710_, 1);
lean_dec(v_unused_742_);
v___x_720_ = v_line_710_;
v_isShared_721_ = v_isSharedCheck_741_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_uri_718_);
lean_dec(v_line_710_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_741_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v_entries_722_; lean_object* v_indexes_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_740_; 
v_entries_722_ = lean_ctor_get(v_headers_711_, 0);
v_indexes_723_ = lean_ctor_get(v_headers_711_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_headers_711_);
if (v_isSharedCheck_740_ == 0)
{
v___x_725_ = v_headers_711_;
v_isShared_726_ = v_isSharedCheck_740_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_indexes_723_);
lean_inc(v_entries_722_);
lean_dec(v_headers_711_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_740_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v_i_727_; lean_object* v___x_728_; lean_object* v_entries_729_; lean_object* v_indexes_730_; lean_object* v___x_732_; 
v_i_727_ = lean_array_get_size(v_entries_722_);
lean_inc_ref(v_key_708_);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v_key_708_);
lean_ctor_set(v___x_728_, 1, v_value_709_);
v_entries_729_ = lean_array_push(v_entries_722_, v___x_728_);
v_indexes_730_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_727_, v_indexes_723_, v_key_708_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v_indexes_730_);
lean_ctor_set(v___x_725_, 0, v_entries_729_);
v___x_732_ = v___x_725_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_entries_729_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_indexes_730_);
v___x_732_ = v_reuseFailAlloc_739_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_734_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v___x_732_);
v___x_734_ = v___x_720_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_uri_718_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_732_);
lean_ctor_set_uint8(v_reuseFailAlloc_738_, sizeof(void*)*2, v_method_716_);
lean_ctor_set_uint8(v_reuseFailAlloc_738_, sizeof(void*)*2 + 1, v_version_717_);
v___x_734_ = v_reuseFailAlloc_738_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_736_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_734_);
v___x_736_ = v___x_714_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_extensions_712_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(lean_object* v_00_u03b2_745_, lean_object* v_a_746_, lean_object* v_x_747_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___redArg(v_a_746_, v_x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0___boxed(lean_object* v_00_u03b2_749_, lean_object* v_a_750_, lean_object* v_x_751_){
_start:
{
uint8_t v_res_752_; lean_object* v_r_753_; 
v_res_752_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__0(v_00_u03b2_749_, v_a_750_, v_x_751_);
lean_dec(v_x_751_);
lean_dec_ref(v_a_750_);
v_r_753_ = lean_box(v_res_752_);
return v_r_753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1(lean_object* v_00_u03b2_754_, lean_object* v_data_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1___redArg(v_data_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_757_, lean_object* v_i_758_, lean_object* v_source_759_, lean_object* v_target_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2___redArg(v_i_758_, v_source_759_, v_target_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_762_, lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0_spec__1_spec__2_spec__3___redArg(v_x_763_, v_x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x21(lean_object* v_builder_766_, lean_object* v_key_767_, lean_object* v_value_768_){
_start:
{
lean_object* v_line_769_; lean_object* v_headers_770_; lean_object* v_extensions_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_804_; 
v_line_769_ = lean_ctor_get(v_builder_766_, 0);
lean_inc_ref(v_line_769_);
v_headers_770_ = lean_ctor_get(v_line_769_, 1);
lean_inc_ref(v_headers_770_);
v_extensions_771_ = lean_ctor_get(v_builder_766_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_builder_766_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; 
v_unused_805_ = lean_ctor_get(v_builder_766_, 0);
lean_dec(v_unused_805_);
v___x_773_ = v_builder_766_;
v_isShared_774_ = v_isSharedCheck_804_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_extensions_771_);
lean_dec(v_builder_766_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_804_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
uint8_t v_method_775_; uint8_t v_version_776_; lean_object* v_uri_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_802_; 
v_method_775_ = lean_ctor_get_uint8(v_line_769_, sizeof(void*)*2);
v_version_776_ = lean_ctor_get_uint8(v_line_769_, sizeof(void*)*2 + 1);
v_uri_777_ = lean_ctor_get(v_line_769_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v_line_769_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v_line_769_, 1);
lean_dec(v_unused_803_);
v___x_779_ = v_line_769_;
v_isShared_780_ = v_isSharedCheck_802_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_uri_777_);
lean_dec(v_line_769_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_802_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v_entries_781_; lean_object* v_indexes_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_801_; 
v_entries_781_ = lean_ctor_get(v_headers_770_, 0);
v_indexes_782_ = lean_ctor_get(v_headers_770_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_headers_770_);
if (v_isSharedCheck_801_ == 0)
{
v___x_784_ = v_headers_770_;
v_isShared_785_ = v_isSharedCheck_801_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_indexes_782_);
lean_inc(v_entries_781_);
lean_dec(v_headers_770_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_801_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_key_786_; lean_object* v_value_787_; lean_object* v_i_788_; lean_object* v___x_789_; lean_object* v_entries_790_; lean_object* v_indexes_791_; lean_object* v___x_793_; 
v_key_786_ = l_Std_Http_Header_Name_ofString_x21(v_key_767_);
v_value_787_ = l_Std_Http_Header_Value_ofString_x21(v_value_768_);
v_i_788_ = lean_array_get_size(v_entries_781_);
lean_inc_ref(v_key_786_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v_key_786_);
lean_ctor_set(v___x_789_, 1, v_value_787_);
v_entries_790_ = lean_array_push(v_entries_781_, v___x_789_);
v_indexes_791_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_788_, v_indexes_782_, v_key_786_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v_indexes_791_);
lean_ctor_set(v___x_784_, 0, v_entries_790_);
v___x_793_ = v___x_784_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_entries_790_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_indexes_791_);
v___x_793_ = v_reuseFailAlloc_800_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v___x_793_);
v___x_795_ = v___x_779_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_uri_777_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_793_);
lean_ctor_set_uint8(v_reuseFailAlloc_799_, sizeof(void*)*2, v_method_775_);
lean_ctor_set_uint8(v_reuseFailAlloc_799_, sizeof(void*)*2 + 1, v_version_776_);
v___x_795_ = v_reuseFailAlloc_799_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_797_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_795_);
v___x_797_ = v___x_773_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_extensions_771_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_header_x3f(lean_object* v_builder_806_, lean_object* v_key_807_, lean_object* v_value_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Std_Http_Header_Name_ofString_x3f(v_key_807_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v___x_810_; 
lean_dec_ref(v_value_808_);
lean_dec_ref(v_builder_806_);
v___x_810_ = lean_box(0);
return v___x_810_;
}
else
{
lean_object* v_val_811_; lean_object* v___x_812_; 
v_val_811_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_val_811_);
lean_dec_ref(v___x_809_);
v___x_812_ = l_Std_Http_Header_Value_ofString_x3f(v_value_808_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v___x_813_; 
lean_dec(v_val_811_);
lean_dec_ref(v_builder_806_);
v___x_813_ = lean_box(0);
return v___x_813_;
}
else
{
lean_object* v_line_814_; lean_object* v_headers_815_; lean_object* v_val_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_856_; 
v_line_814_ = lean_ctor_get(v_builder_806_, 0);
lean_inc_ref(v_line_814_);
v_headers_815_ = lean_ctor_get(v_line_814_, 1);
lean_inc_ref(v_headers_815_);
v_val_816_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_856_ == 0)
{
v___x_818_ = v___x_812_;
v_isShared_819_ = v_isSharedCheck_856_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_val_816_);
lean_dec(v___x_812_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_856_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v_extensions_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_854_; 
v_extensions_820_ = lean_ctor_get(v_builder_806_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v_builder_806_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v_builder_806_, 0);
lean_dec(v_unused_855_);
v___x_822_ = v_builder_806_;
v_isShared_823_ = v_isSharedCheck_854_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_extensions_820_);
lean_dec(v_builder_806_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_854_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
uint8_t v_method_824_; uint8_t v_version_825_; lean_object* v_uri_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_852_; 
v_method_824_ = lean_ctor_get_uint8(v_line_814_, sizeof(void*)*2);
v_version_825_ = lean_ctor_get_uint8(v_line_814_, sizeof(void*)*2 + 1);
v_uri_826_ = lean_ctor_get(v_line_814_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v_line_814_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v_line_814_, 1);
lean_dec(v_unused_853_);
v___x_828_ = v_line_814_;
v_isShared_829_ = v_isSharedCheck_852_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_uri_826_);
lean_dec(v_line_814_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_852_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v_entries_830_; lean_object* v_indexes_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_851_; 
v_entries_830_ = lean_ctor_get(v_headers_815_, 0);
v_indexes_831_ = lean_ctor_get(v_headers_815_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v_headers_815_);
if (v_isSharedCheck_851_ == 0)
{
v___x_833_ = v_headers_815_;
v_isShared_834_ = v_isSharedCheck_851_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_indexes_831_);
lean_inc(v_entries_830_);
lean_dec(v_headers_815_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_851_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v_i_835_; lean_object* v___x_836_; lean_object* v_entries_837_; lean_object* v_indexes_838_; lean_object* v___x_840_; 
v_i_835_ = lean_array_get_size(v_entries_830_);
lean_inc(v_val_811_);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v_val_811_);
lean_ctor_set(v___x_836_, 1, v_val_816_);
v_entries_837_ = lean_array_push(v_entries_830_, v___x_836_);
v_indexes_838_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Http_Request_Builder_header_spec__0(v_i_835_, v_indexes_831_, v_val_811_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v_indexes_838_);
lean_ctor_set(v___x_833_, 0, v_entries_837_);
v___x_840_ = v___x_833_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_entries_837_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_indexes_838_);
v___x_840_ = v_reuseFailAlloc_850_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_842_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v___x_840_);
v___x_842_ = v___x_828_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_uri_826_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v___x_840_);
lean_ctor_set_uint8(v_reuseFailAlloc_849_, sizeof(void*)*2, v_method_824_);
lean_ctor_set_uint8(v_reuseFailAlloc_849_, sizeof(void*)*2 + 1, v_version_825_);
v___x_842_ = v_reuseFailAlloc_849_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_844_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_842_);
v___x_844_ = v___x_822_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_extensions_820_);
v___x_844_ = v_reuseFailAlloc_848_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_846_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_844_);
v___x_846_ = v___x_818_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
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
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_headerOpt(lean_object* v_builder_857_, lean_object* v_key_858_, lean_object* v_value_859_){
_start:
{
if (lean_obj_tag(v_value_859_) == 0)
{
lean_dec_ref(v_key_858_);
return v_builder_857_;
}
else
{
lean_object* v_val_860_; lean_object* v___x_861_; 
v_val_860_ = lean_ctor_get(v_value_859_, 0);
lean_inc(v_val_860_);
lean_dec_ref(v_value_859_);
v___x_861_ = l_Std_Http_Request_Builder_header(v_builder_857_, v_key_858_, v_val_860_);
return v___x_861_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension___redArg(lean_object* v_builder_863_, lean_object* v_inst_864_, lean_object* v_data_865_){
_start:
{
lean_object* v_line_866_; lean_object* v_extensions_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_878_; 
v_line_866_ = lean_ctor_get(v_builder_863_, 0);
v_extensions_867_ = lean_ctor_get(v_builder_863_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v_builder_863_);
if (v_isSharedCheck_878_ == 0)
{
v___x_869_ = v_builder_863_;
v_isShared_870_ = v_isSharedCheck_878_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_extensions_867_);
lean_inc(v_line_866_);
lean_dec(v_builder_863_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_878_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v_dyn_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v_dyn_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_871_, 0, v_inst_864_);
lean_ctor_set(v_dyn_871_, 1, v_data_865_);
v___x_872_ = ((lean_object*)(l_Std_Http_Request_Builder_extension___redArg___closed__0));
v___x_873_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_871_);
v___x_874_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_872_, v___x_873_, v_dyn_871_, v_extensions_867_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 1, v___x_874_);
v___x_876_ = v___x_869_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_line_866_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension(lean_object* v_00_u03b1_879_, lean_object* v_builder_880_, lean_object* v_inst_881_, lean_object* v_data_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Std_Http_Request_Builder_extension___redArg(v_builder_880_, v_inst_881_, v_data_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object* v_builder_884_, lean_object* v_body_885_){
_start:
{
lean_object* v_line_886_; lean_object* v_extensions_887_; lean_object* v___x_888_; 
v_line_886_ = lean_ctor_get(v_builder_884_, 0);
v_extensions_887_ = lean_ctor_get(v_builder_884_, 1);
lean_inc(v_extensions_887_);
lean_inc_ref(v_line_886_);
v___x_888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_888_, 0, v_line_886_);
lean_ctor_set(v___x_888_, 1, v_body_885_);
lean_ctor_set(v___x_888_, 2, v_extensions_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg___boxed(lean_object* v_builder_889_, lean_object* v_body_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Std_Http_Request_Builder_body___redArg(v_builder_889_, v_body_890_);
lean_dec_ref(v_builder_889_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body(lean_object* v_t_892_, lean_object* v_builder_893_, lean_object* v_body_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Std_Http_Request_Builder_body___redArg(v_builder_893_, v_body_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___boxed(lean_object* v_t_896_, lean_object* v_builder_897_, lean_object* v_body_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Std_Http_Request_Builder_body(v_t_896_, v_builder_897_, v_body_898_);
lean_dec_ref(v_builder_897_);
return v_res_899_;
}
}
static lean_object* _init_l_Std_Http_Request_get___closed__0(void){
_start:
{
uint8_t v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_900_ = 8;
v___x_901_ = l_Std_Http_Request_new;
v___x_902_ = l_Std_Http_Request_Builder_method(v___x_901_, v___x_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_get(lean_object* v_uri_903_){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_obj_once(&l_Std_Http_Request_get___closed__0, &l_Std_Http_Request_get___closed__0_once, _init_l_Std_Http_Request_get___closed__0);
v___x_905_ = l_Std_Http_Request_Builder_uri(v___x_904_, v_uri_903_);
return v___x_905_;
}
}
static lean_object* _init_l_Std_Http_Request_post___closed__0(void){
_start:
{
uint8_t v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = 23;
v___x_907_ = l_Std_Http_Request_new;
v___x_908_ = l_Std_Http_Request_Builder_method(v___x_907_, v___x_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_post(lean_object* v_uri_909_){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_obj_once(&l_Std_Http_Request_post___closed__0, &l_Std_Http_Request_post___closed__0_once, _init_l_Std_Http_Request_post___closed__0);
v___x_911_ = l_Std_Http_Request_Builder_uri(v___x_910_, v_uri_909_);
return v___x_911_;
}
}
static lean_object* _init_l_Std_Http_Request_put___closed__0(void){
_start:
{
uint8_t v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_912_ = 27;
v___x_913_ = l_Std_Http_Request_new;
v___x_914_ = l_Std_Http_Request_Builder_method(v___x_913_, v___x_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_put(lean_object* v_uri_915_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_obj_once(&l_Std_Http_Request_put___closed__0, &l_Std_Http_Request_put___closed__0_once, _init_l_Std_Http_Request_put___closed__0);
v___x_917_ = l_Std_Http_Request_Builder_uri(v___x_916_, v_uri_915_);
return v___x_917_;
}
}
static lean_object* _init_l_Std_Http_Request_delete___closed__0(void){
_start:
{
uint8_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_918_ = 7;
v___x_919_ = l_Std_Http_Request_new;
v___x_920_ = l_Std_Http_Request_Builder_method(v___x_919_, v___x_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_delete(lean_object* v_uri_921_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_obj_once(&l_Std_Http_Request_delete___closed__0, &l_Std_Http_Request_delete___closed__0_once, _init_l_Std_Http_Request_delete___closed__0);
v___x_923_ = l_Std_Http_Request_Builder_uri(v___x_922_, v_uri_921_);
return v___x_923_;
}
}
static lean_object* _init_l_Std_Http_Request_patch___closed__0(void){
_start:
{
uint8_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_924_ = 22;
v___x_925_ = l_Std_Http_Request_new;
v___x_926_ = l_Std_Http_Request_Builder_method(v___x_925_, v___x_924_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_patch(lean_object* v_uri_927_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_obj_once(&l_Std_Http_Request_patch___closed__0, &l_Std_Http_Request_patch___closed__0_once, _init_l_Std_Http_Request_patch___closed__0);
v___x_929_ = l_Std_Http_Request_Builder_uri(v___x_928_, v_uri_927_);
return v___x_929_;
}
}
static lean_object* _init_l_Std_Http_Request_head___closed__0(void){
_start:
{
uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = 9;
v___x_931_ = l_Std_Http_Request_new;
v___x_932_ = l_Std_Http_Request_Builder_method(v___x_931_, v___x_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_head(lean_object* v_uri_933_){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_obj_once(&l_Std_Http_Request_head___closed__0, &l_Std_Http_Request_head___closed__0_once, _init_l_Std_Http_Request_head___closed__0);
v___x_935_ = l_Std_Http_Request_Builder_uri(v___x_934_, v_uri_933_);
return v___x_935_;
}
}
static lean_object* _init_l_Std_Http_Request_options___closed__0(void){
_start:
{
uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = 20;
v___x_937_ = l_Std_Http_Request_new;
v___x_938_ = l_Std_Http_Request_Builder_method(v___x_937_, v___x_936_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_options(lean_object* v_uri_939_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_obj_once(&l_Std_Http_Request_options___closed__0, &l_Std_Http_Request_options___closed__0_once, _init_l_Std_Http_Request_options___closed__0);
v___x_941_ = l_Std_Http_Request_Builder_uri(v___x_940_, v_uri_939_);
return v___x_941_;
}
}
static lean_object* _init_l_Std_Http_Request_connect___closed__0(void){
_start:
{
uint8_t v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_942_ = 5;
v___x_943_ = l_Std_Http_Request_new;
v___x_944_ = l_Std_Http_Request_Builder_method(v___x_943_, v___x_942_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_connect(lean_object* v_uri_945_){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_obj_once(&l_Std_Http_Request_connect___closed__0, &l_Std_Http_Request_connect___closed__0_once, _init_l_Std_Http_Request_connect___closed__0);
v___x_947_ = l_Std_Http_Request_Builder_uri(v___x_946_, v_uri_945_);
return v___x_947_;
}
}
static lean_object* _init_l_Std_Http_Request_trace___closed__0(void){
_start:
{
uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = 32;
v___x_949_ = l_Std_Http_Request_new;
v___x_950_ = l_Std_Http_Request_Builder_method(v___x_949_, v___x_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_trace(lean_object* v_uri_951_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_obj_once(&l_Std_Http_Request_trace___closed__0, &l_Std_Http_Request_trace___closed__0_once, _init_l_Std_Http_Request_trace___closed__0);
v___x_953_ = l_Std_Http_Request_Builder_uri(v___x_952_, v_uri_951_);
return v___x_953_;
}
}
lean_object* runtime_initialize_Std_Internal_Http_Data_Extensions(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Method(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Version(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Headers(uint8_t builtin);
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
