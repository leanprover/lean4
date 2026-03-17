// Lean compiler output
// Module: Std.Internal.Http.Data.Request
// Imports: public import Std.Internal.Http.Data.Extensions public import Std.Internal.Http.Data.Method public import Std.Internal.Http.Data.Version
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
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Extensions_empty;
extern lean_object* l_Std_Http_instInhabitedExtensions_default;
lean_object* l_Std_Http_instReprMethod_repr(uint8_t, lean_object*);
lean_object* l_Std_Http_instReprVersion_repr(uint8_t, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Http_Extensions_compareName___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Request_instInhabitedHead_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Request_instInhabitedHead_default___closed__0 = (const lean_object*)&l_Std_Http_Request_instInhabitedHead_default___closed__0_value;
static const lean_ctor_object l_Std_Http_Request_instInhabitedHead_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Request_instInhabitedHead_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_Request_instInhabitedHead_default___closed__1 = (const lean_object*)&l_Std_Http_Request_instInhabitedHead_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Request_instInhabitedHead_default = (const lean_object*)&l_Std_Http_Request_instInhabitedHead_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Request_instInhabitedHead = (const lean_object*)&l_Std_Http_Request_instInhabitedHead_default___closed__1_value;
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
static const lean_string_object l_Std_Http_Request_instReprHead_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__16 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__16_value;
static lean_once_cell_t l_Std_Http_Request_instReprHead_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__17;
static lean_once_cell_t l_Std_Http_Request_instReprHead_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__18;
static const lean_ctor_object l_Std_Http_Request_instReprHead_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__19 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__19_value;
static const lean_ctor_object l_Std_Http_Request_instReprHead_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__16_value)}};
static const lean_object* l_Std_Http_Request_instReprHead_repr___redArg___closed__20 = (const lean_object*)&l_Std_Http_Request_instReprHead_repr___redArg___closed__20_value;
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
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__0_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__1_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.0"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__2 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__2_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.1"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__3 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__3_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/2.0"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__4 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__4_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/3.0"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__5 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__5_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ACL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__6 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__6_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "BASELINE-CONTROL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__7 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__7_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "BIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__8 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__8_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CHECKIN"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__9 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__9_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CHECKOUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__10 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__10_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CONNECT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__11 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__11_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "COPY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__12 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__12_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "DELETE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__13 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__13_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__14 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__14_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__15 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__15_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "LABEL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__16 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__16_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LINK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__17 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__17_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LOCK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__18 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__18_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MERGE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__19 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__19_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKACTIVITY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__20 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__20_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "MKCALENDAR"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__21 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__21_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "MKCOL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__22 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__22_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MKREDIRECTREF"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__23 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__23_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MKWORKSPACE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__24 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__24_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MOVE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__25 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__25_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "OPTIONS"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__26 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__26_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ORDERPATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__27 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__27_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__28 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__28_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__29 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__29_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PRI"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__30 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__30_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PROPFIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__31 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__31_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PROPPATCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__32 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__32_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__33 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__33_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "QUERY"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__34 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__34_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REBIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__35 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__35_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "REPORT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__36 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__36_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SEARCH"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__37 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__37_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "TRACE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__38 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__38_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNBIND"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__39 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__39_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "UNCHECKOUT"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__40 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__40_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLINK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__41 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__41_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UNLOCK"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__42 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__42_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UPDATE"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__43 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__43_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "UPDATEREDIRECTREF"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__44 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__44_value;
static const lean_string_object l_Std_Http_Request_instToStringHead___lam__0___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "VERSION-CONTROL"};
static const lean_object* l_Std_Http_Request_instToStringHead___lam__0___closed__45 = (const lean_object*)&l_Std_Http_Request_instToStringHead___lam__0___closed__45_value;
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_Request_instToStringHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instToStringHead___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instToStringHead___closed__0 = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Request_instToStringHead = (const lean_object*)&l_Std_Http_Request_instToStringHead___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Request_instEncodeV11Head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Request_instEncodeV11Head___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Request_instEncodeV11Head___closed__0 = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Request_instEncodeV11Head = (const lean_object*)&l_Std_Http_Request_instEncodeV11Head___closed__0_value;
static const lean_string_object l_Std_Http_Request_new___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Std_Http_Request_new___closed__0 = (const lean_object*)&l_Std_Http_Request_new___closed__0_value;
static const lean_ctor_object l_Std_Http_Request_new___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Request_new___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_Request_new___closed__1 = (const lean_object*)&l_Std_Http_Request_new___closed__1_value;
static lean_once_cell_t l_Std_Http_Request_new___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Request_new___closed__2;
LEAN_EXPORT lean_object* l_Std_Http_Request_new;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_empty;
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri(lean_object*, lean_object*);
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
static lean_object* _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__0));
v___x_40_ = lean_string_length(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_obj_once(&l_Std_Http_Request_instReprHead_repr___redArg___closed__17, &l_Std_Http_Request_instReprHead_repr___redArg___closed__17_once, _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__17);
v___x_42_ = lean_nat_to_int(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instReprHead_repr___redArg(lean_object* v_x_47_){
_start:
{
uint8_t v_method_48_; uint8_t v_version_49_; lean_object* v_uri_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v_method_48_ = lean_ctor_get_uint8(v_x_47_, sizeof(void*)*1);
v_version_49_ = lean_ctor_get_uint8(v_x_47_, sizeof(void*)*1 + 1);
v_uri_50_ = lean_ctor_get(v_x_47_, 0);
lean_inc_ref(v_uri_50_);
lean_dec_ref(v_x_47_);
v___x_51_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__5));
v___x_52_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__6));
v___x_53_ = lean_obj_once(&l_Std_Http_Request_instReprHead_repr___redArg___closed__7, &l_Std_Http_Request_instReprHead_repr___redArg___closed__7_once, _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__7);
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = l_Std_Http_instReprMethod_repr(v_method_48_, v___x_54_);
v___x_56_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_53_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = 0;
v___x_58_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set_uint8(v___x_58_, sizeof(void*)*1, v___x_57_);
v___x_59_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_52_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
v___x_60_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__9));
v___x_61_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_59_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = lean_box(1);
v___x_63_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_61_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__11));
v___x_65_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
v___x_66_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_51_);
v___x_67_ = lean_obj_once(&l_Std_Http_Request_instReprHead_repr___redArg___closed__12, &l_Std_Http_Request_instReprHead_repr___redArg___closed__12_once, _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__12);
v___x_68_ = l_Std_Http_instReprVersion_repr(v_version_49_, v___x_54_);
v___x_69_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*1, v___x_57_);
v___x_71_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_66_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_60_);
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_62_);
v___x_74_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__14));
v___x_75_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_51_);
v___x_77_ = lean_obj_once(&l_Std_Http_Request_instReprHead_repr___redArg___closed__15, &l_Std_Http_Request_instReprHead_repr___redArg___closed__15_once, _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__15);
v___x_78_ = l_String_quote(v_uri_50_);
v___x_79_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
v___x_80_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_77_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*1, v___x_57_);
v___x_82_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_76_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = lean_obj_once(&l_Std_Http_Request_instReprHead_repr___redArg___closed__18, &l_Std_Http_Request_instReprHead_repr___redArg___closed__18_once, _init_l_Std_Http_Request_instReprHead_repr___redArg___closed__18);
v___x_84_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__19));
v___x_85_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___x_82_);
v___x_86_ = ((lean_object*)(l_Std_Http_Request_instReprHead_repr___redArg___closed__20));
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_83_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_57_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instReprHead_repr(lean_object* v_x_90_, lean_object* v_prec_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Std_Http_Request_instReprHead_repr___redArg(v_x_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instReprHead_repr___boxed(lean_object* v_x_93_, lean_object* v_prec_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Std_Http_Request_instReprHead_repr(v_x_93_, v_prec_94_);
lean_dec(v_prec_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest_default___redArg(lean_object* v_inst_98_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = ((lean_object*)(l_Std_Http_Request_instInhabitedHead_default));
v___x_100_ = l_Std_Http_instInhabitedExtensions_default;
v___x_101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_101_, 0, v___x_99_);
lean_ctor_set(v___x_101_, 1, v_inst_98_);
lean_ctor_set(v___x_101_, 2, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest_default(lean_object* v_a_102_, lean_object* v_inst_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Std_Http_instInhabitedRequest_default___redArg(v_inst_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest___redArg(lean_object* v_inst_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Std_Http_instInhabitedRequest_default___redArg(v_inst_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedRequest(lean_object* v_a_107_, lean_object* v_inst_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Std_Http_instInhabitedRequest_default___redArg(v_inst_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__0(lean_object* v_req_156_){
_start:
{
lean_object* v___y_158_; lean_object* v___y_159_; uint8_t v_method_163_; uint8_t v_version_164_; lean_object* v_uri_165_; lean_object* v___y_167_; 
v_method_163_ = lean_ctor_get_uint8(v_req_156_, sizeof(void*)*1);
v_version_164_ = lean_ctor_get_uint8(v_req_156_, sizeof(void*)*1 + 1);
v_uri_165_ = lean_ctor_get(v_req_156_, 0);
switch(v_method_163_)
{
case 0:
{
lean_object* v___x_176_; 
v___x_176_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__6));
v___y_167_ = v___x_176_;
goto v___jp_166_;
}
case 1:
{
lean_object* v___x_177_; 
v___x_177_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__7));
v___y_167_ = v___x_177_;
goto v___jp_166_;
}
case 2:
{
lean_object* v___x_178_; 
v___x_178_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__8));
v___y_167_ = v___x_178_;
goto v___jp_166_;
}
case 3:
{
lean_object* v___x_179_; 
v___x_179_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__9));
v___y_167_ = v___x_179_;
goto v___jp_166_;
}
case 4:
{
lean_object* v___x_180_; 
v___x_180_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__10));
v___y_167_ = v___x_180_;
goto v___jp_166_;
}
case 5:
{
lean_object* v___x_181_; 
v___x_181_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__11));
v___y_167_ = v___x_181_;
goto v___jp_166_;
}
case 6:
{
lean_object* v___x_182_; 
v___x_182_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__12));
v___y_167_ = v___x_182_;
goto v___jp_166_;
}
case 7:
{
lean_object* v___x_183_; 
v___x_183_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__13));
v___y_167_ = v___x_183_;
goto v___jp_166_;
}
case 8:
{
lean_object* v___x_184_; 
v___x_184_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__14));
v___y_167_ = v___x_184_;
goto v___jp_166_;
}
case 9:
{
lean_object* v___x_185_; 
v___x_185_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__15));
v___y_167_ = v___x_185_;
goto v___jp_166_;
}
case 10:
{
lean_object* v___x_186_; 
v___x_186_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__16));
v___y_167_ = v___x_186_;
goto v___jp_166_;
}
case 11:
{
lean_object* v___x_187_; 
v___x_187_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__17));
v___y_167_ = v___x_187_;
goto v___jp_166_;
}
case 12:
{
lean_object* v___x_188_; 
v___x_188_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__18));
v___y_167_ = v___x_188_;
goto v___jp_166_;
}
case 13:
{
lean_object* v___x_189_; 
v___x_189_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__19));
v___y_167_ = v___x_189_;
goto v___jp_166_;
}
case 14:
{
lean_object* v___x_190_; 
v___x_190_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__20));
v___y_167_ = v___x_190_;
goto v___jp_166_;
}
case 15:
{
lean_object* v___x_191_; 
v___x_191_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__21));
v___y_167_ = v___x_191_;
goto v___jp_166_;
}
case 16:
{
lean_object* v___x_192_; 
v___x_192_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__22));
v___y_167_ = v___x_192_;
goto v___jp_166_;
}
case 17:
{
lean_object* v___x_193_; 
v___x_193_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__23));
v___y_167_ = v___x_193_;
goto v___jp_166_;
}
case 18:
{
lean_object* v___x_194_; 
v___x_194_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__24));
v___y_167_ = v___x_194_;
goto v___jp_166_;
}
case 19:
{
lean_object* v___x_195_; 
v___x_195_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__25));
v___y_167_ = v___x_195_;
goto v___jp_166_;
}
case 20:
{
lean_object* v___x_196_; 
v___x_196_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__26));
v___y_167_ = v___x_196_;
goto v___jp_166_;
}
case 21:
{
lean_object* v___x_197_; 
v___x_197_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__27));
v___y_167_ = v___x_197_;
goto v___jp_166_;
}
case 22:
{
lean_object* v___x_198_; 
v___x_198_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__28));
v___y_167_ = v___x_198_;
goto v___jp_166_;
}
case 23:
{
lean_object* v___x_199_; 
v___x_199_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__29));
v___y_167_ = v___x_199_;
goto v___jp_166_;
}
case 24:
{
lean_object* v___x_200_; 
v___x_200_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__30));
v___y_167_ = v___x_200_;
goto v___jp_166_;
}
case 25:
{
lean_object* v___x_201_; 
v___x_201_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__31));
v___y_167_ = v___x_201_;
goto v___jp_166_;
}
case 26:
{
lean_object* v___x_202_; 
v___x_202_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__32));
v___y_167_ = v___x_202_;
goto v___jp_166_;
}
case 27:
{
lean_object* v___x_203_; 
v___x_203_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__33));
v___y_167_ = v___x_203_;
goto v___jp_166_;
}
case 28:
{
lean_object* v___x_204_; 
v___x_204_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__34));
v___y_167_ = v___x_204_;
goto v___jp_166_;
}
case 29:
{
lean_object* v___x_205_; 
v___x_205_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__35));
v___y_167_ = v___x_205_;
goto v___jp_166_;
}
case 30:
{
lean_object* v___x_206_; 
v___x_206_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__36));
v___y_167_ = v___x_206_;
goto v___jp_166_;
}
case 31:
{
lean_object* v___x_207_; 
v___x_207_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__37));
v___y_167_ = v___x_207_;
goto v___jp_166_;
}
case 32:
{
lean_object* v___x_208_; 
v___x_208_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__38));
v___y_167_ = v___x_208_;
goto v___jp_166_;
}
case 33:
{
lean_object* v___x_209_; 
v___x_209_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__39));
v___y_167_ = v___x_209_;
goto v___jp_166_;
}
case 34:
{
lean_object* v___x_210_; 
v___x_210_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__40));
v___y_167_ = v___x_210_;
goto v___jp_166_;
}
case 35:
{
lean_object* v___x_211_; 
v___x_211_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__41));
v___y_167_ = v___x_211_;
goto v___jp_166_;
}
case 36:
{
lean_object* v___x_212_; 
v___x_212_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__42));
v___y_167_ = v___x_212_;
goto v___jp_166_;
}
case 37:
{
lean_object* v___x_213_; 
v___x_213_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__43));
v___y_167_ = v___x_213_;
goto v___jp_166_;
}
case 38:
{
lean_object* v___x_214_; 
v___x_214_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__44));
v___y_167_ = v___x_214_;
goto v___jp_166_;
}
default: 
{
lean_object* v___x_215_; 
v___x_215_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__45));
v___y_167_ = v___x_215_;
goto v___jp_166_;
}
}
v___jp_157_:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_string_append(v___y_158_, v___y_159_);
lean_dec_ref(v___y_159_);
v___x_161_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__0));
v___x_162_ = lean_string_append(v___x_160_, v___x_161_);
return v___x_162_;
}
v___jp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__1));
v___x_169_ = lean_string_append(v___y_167_, v___x_168_);
v___x_170_ = lean_string_append(v___x_169_, v_uri_165_);
v___x_171_ = lean_string_append(v___x_170_, v___x_168_);
switch(v_version_164_)
{
case 0:
{
lean_object* v___x_172_; 
v___x_172_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__2));
v___y_158_ = v___x_171_;
v___y_159_ = v___x_172_;
goto v___jp_157_;
}
case 1:
{
lean_object* v___x_173_; 
v___x_173_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__3));
v___y_158_ = v___x_171_;
v___y_159_ = v___x_173_;
goto v___jp_157_;
}
case 2:
{
lean_object* v___x_174_; 
v___x_174_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__4));
v___y_158_ = v___x_171_;
v___y_159_ = v___x_174_;
goto v___jp_157_;
}
default: 
{
lean_object* v___x_175_; 
v___x_175_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__5));
v___y_158_ = v___x_171_;
v___y_159_ = v___x_175_;
goto v___jp_157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instToStringHead___lam__0___boxed(lean_object* v_req_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Std_Http_Request_instToStringHead___lam__0(v_req_216_);
lean_dec_ref(v_req_216_);
return v_res_217_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__0));
v___x_221_ = lean_string_to_utf8(v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0);
v___x_223_ = lean_byte_array_size(v___x_222_);
return v___x_223_;
}
}
static uint8_t _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__2(void){
_start:
{
uint32_t v___x_224_; uint8_t v___x_225_; 
v___x_224_ = 32;
v___x_225_ = lean_uint32_to_uint8(v___x_224_);
return v___x_225_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3(void){
_start:
{
uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_226_ = lean_uint8_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__2, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__2_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__2);
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_mk_empty_array_with_capacity(v___x_227_);
v___x_229_ = lean_box(v___x_226_);
v___x_230_ = lean_array_push(v___x_228_, v___x_229_);
v___x_231_ = lean_byte_array_mk(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3);
v___x_233_ = lean_byte_array_size(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0(lean_object* v_buffer_234_, lean_object* v_req_235_){
_start:
{
lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; uint8_t v_method_249_; uint8_t v_version_250_; lean_object* v_uri_251_; lean_object* v___y_253_; 
v_method_249_ = lean_ctor_get_uint8(v_req_235_, sizeof(void*)*1);
v_version_250_ = lean_ctor_get_uint8(v_req_235_, sizeof(void*)*1 + 1);
v_uri_251_ = lean_ctor_get(v_req_235_, 0);
switch(v_method_249_)
{
case 0:
{
lean_object* v___x_274_; 
v___x_274_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__6));
v___y_253_ = v___x_274_;
goto v___jp_252_;
}
case 1:
{
lean_object* v___x_275_; 
v___x_275_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__7));
v___y_253_ = v___x_275_;
goto v___jp_252_;
}
case 2:
{
lean_object* v___x_276_; 
v___x_276_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__8));
v___y_253_ = v___x_276_;
goto v___jp_252_;
}
case 3:
{
lean_object* v___x_277_; 
v___x_277_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__9));
v___y_253_ = v___x_277_;
goto v___jp_252_;
}
case 4:
{
lean_object* v___x_278_; 
v___x_278_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__10));
v___y_253_ = v___x_278_;
goto v___jp_252_;
}
case 5:
{
lean_object* v___x_279_; 
v___x_279_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__11));
v___y_253_ = v___x_279_;
goto v___jp_252_;
}
case 6:
{
lean_object* v___x_280_; 
v___x_280_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__12));
v___y_253_ = v___x_280_;
goto v___jp_252_;
}
case 7:
{
lean_object* v___x_281_; 
v___x_281_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__13));
v___y_253_ = v___x_281_;
goto v___jp_252_;
}
case 8:
{
lean_object* v___x_282_; 
v___x_282_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__14));
v___y_253_ = v___x_282_;
goto v___jp_252_;
}
case 9:
{
lean_object* v___x_283_; 
v___x_283_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__15));
v___y_253_ = v___x_283_;
goto v___jp_252_;
}
case 10:
{
lean_object* v___x_284_; 
v___x_284_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__16));
v___y_253_ = v___x_284_;
goto v___jp_252_;
}
case 11:
{
lean_object* v___x_285_; 
v___x_285_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__17));
v___y_253_ = v___x_285_;
goto v___jp_252_;
}
case 12:
{
lean_object* v___x_286_; 
v___x_286_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__18));
v___y_253_ = v___x_286_;
goto v___jp_252_;
}
case 13:
{
lean_object* v___x_287_; 
v___x_287_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__19));
v___y_253_ = v___x_287_;
goto v___jp_252_;
}
case 14:
{
lean_object* v___x_288_; 
v___x_288_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__20));
v___y_253_ = v___x_288_;
goto v___jp_252_;
}
case 15:
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__21));
v___y_253_ = v___x_289_;
goto v___jp_252_;
}
case 16:
{
lean_object* v___x_290_; 
v___x_290_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__22));
v___y_253_ = v___x_290_;
goto v___jp_252_;
}
case 17:
{
lean_object* v___x_291_; 
v___x_291_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__23));
v___y_253_ = v___x_291_;
goto v___jp_252_;
}
case 18:
{
lean_object* v___x_292_; 
v___x_292_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__24));
v___y_253_ = v___x_292_;
goto v___jp_252_;
}
case 19:
{
lean_object* v___x_293_; 
v___x_293_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__25));
v___y_253_ = v___x_293_;
goto v___jp_252_;
}
case 20:
{
lean_object* v___x_294_; 
v___x_294_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__26));
v___y_253_ = v___x_294_;
goto v___jp_252_;
}
case 21:
{
lean_object* v___x_295_; 
v___x_295_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__27));
v___y_253_ = v___x_295_;
goto v___jp_252_;
}
case 22:
{
lean_object* v___x_296_; 
v___x_296_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__28));
v___y_253_ = v___x_296_;
goto v___jp_252_;
}
case 23:
{
lean_object* v___x_297_; 
v___x_297_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__29));
v___y_253_ = v___x_297_;
goto v___jp_252_;
}
case 24:
{
lean_object* v___x_298_; 
v___x_298_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__30));
v___y_253_ = v___x_298_;
goto v___jp_252_;
}
case 25:
{
lean_object* v___x_299_; 
v___x_299_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__31));
v___y_253_ = v___x_299_;
goto v___jp_252_;
}
case 26:
{
lean_object* v___x_300_; 
v___x_300_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__32));
v___y_253_ = v___x_300_;
goto v___jp_252_;
}
case 27:
{
lean_object* v___x_301_; 
v___x_301_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__33));
v___y_253_ = v___x_301_;
goto v___jp_252_;
}
case 28:
{
lean_object* v___x_302_; 
v___x_302_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__34));
v___y_253_ = v___x_302_;
goto v___jp_252_;
}
case 29:
{
lean_object* v___x_303_; 
v___x_303_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__35));
v___y_253_ = v___x_303_;
goto v___jp_252_;
}
case 30:
{
lean_object* v___x_304_; 
v___x_304_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__36));
v___y_253_ = v___x_304_;
goto v___jp_252_;
}
case 31:
{
lean_object* v___x_305_; 
v___x_305_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__37));
v___y_253_ = v___x_305_;
goto v___jp_252_;
}
case 32:
{
lean_object* v___x_306_; 
v___x_306_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__38));
v___y_253_ = v___x_306_;
goto v___jp_252_;
}
case 33:
{
lean_object* v___x_307_; 
v___x_307_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__39));
v___y_253_ = v___x_307_;
goto v___jp_252_;
}
case 34:
{
lean_object* v___x_308_; 
v___x_308_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__40));
v___y_253_ = v___x_308_;
goto v___jp_252_;
}
case 35:
{
lean_object* v___x_309_; 
v___x_309_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__41));
v___y_253_ = v___x_309_;
goto v___jp_252_;
}
case 36:
{
lean_object* v___x_310_; 
v___x_310_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__42));
v___y_253_ = v___x_310_;
goto v___jp_252_;
}
case 37:
{
lean_object* v___x_311_; 
v___x_311_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__43));
v___y_253_ = v___x_311_;
goto v___jp_252_;
}
case 38:
{
lean_object* v___x_312_; 
v___x_312_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__44));
v___y_253_ = v___x_312_;
goto v___jp_252_;
}
default: 
{
lean_object* v___x_313_; 
v___x_313_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__45));
v___y_253_ = v___x_313_;
goto v___jp_252_;
}
}
v___jp_236_:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_240_ = lean_string_to_utf8(v___y_239_);
lean_dec_ref(v___y_239_);
lean_inc_ref(v___x_240_);
v___x_241_ = lean_array_push(v___y_237_, v___x_240_);
v___x_242_ = lean_byte_array_size(v___x_240_);
lean_dec_ref(v___x_240_);
v___x_243_ = lean_nat_add(v___y_238_, v___x_242_);
lean_dec(v___y_238_);
v___x_244_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__0);
v___x_245_ = lean_array_push(v___x_241_, v___x_244_);
v___x_246_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__1);
v___x_247_ = lean_nat_add(v___x_243_, v___x_246_);
lean_dec(v___x_243_);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_245_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
return v___x_248_;
}
v___jp_252_:
{
lean_object* v_data_254_; lean_object* v_size_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_data_254_ = lean_ctor_get(v_buffer_234_, 0);
lean_inc_ref(v_data_254_);
v_size_255_ = lean_ctor_get(v_buffer_234_, 1);
lean_inc(v_size_255_);
lean_dec_ref(v_buffer_234_);
v___x_256_ = lean_string_to_utf8(v___y_253_);
lean_dec_ref(v___y_253_);
lean_inc_ref(v___x_256_);
v___x_257_ = lean_array_push(v_data_254_, v___x_256_);
v___x_258_ = lean_byte_array_size(v___x_256_);
lean_dec_ref(v___x_256_);
v___x_259_ = lean_nat_add(v_size_255_, v___x_258_);
lean_dec(v_size_255_);
v___x_260_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__3);
v___x_261_ = lean_array_push(v___x_257_, v___x_260_);
v___x_262_ = lean_obj_once(&l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4, &l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4_once, _init_l_Std_Http_Request_instEncodeV11Head___lam__0___closed__4);
v___x_263_ = lean_nat_add(v___x_259_, v___x_262_);
lean_dec(v___x_259_);
v___x_264_ = lean_string_to_utf8(v_uri_251_);
lean_inc_ref(v___x_264_);
v___x_265_ = lean_array_push(v___x_261_, v___x_264_);
v___x_266_ = lean_byte_array_size(v___x_264_);
lean_dec_ref(v___x_264_);
v___x_267_ = lean_nat_add(v___x_263_, v___x_266_);
lean_dec(v___x_263_);
v___x_268_ = lean_array_push(v___x_265_, v___x_260_);
v___x_269_ = lean_nat_add(v___x_267_, v___x_262_);
lean_dec(v___x_267_);
switch(v_version_250_)
{
case 0:
{
lean_object* v___x_270_; 
v___x_270_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__2));
v___y_237_ = v___x_268_;
v___y_238_ = v___x_269_;
v___y_239_ = v___x_270_;
goto v___jp_236_;
}
case 1:
{
lean_object* v___x_271_; 
v___x_271_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__3));
v___y_237_ = v___x_268_;
v___y_238_ = v___x_269_;
v___y_239_ = v___x_271_;
goto v___jp_236_;
}
case 2:
{
lean_object* v___x_272_; 
v___x_272_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__4));
v___y_237_ = v___x_268_;
v___y_238_ = v___x_269_;
v___y_239_ = v___x_272_;
goto v___jp_236_;
}
default: 
{
lean_object* v___x_273_; 
v___x_273_ = ((lean_object*)(l_Std_Http_Request_instToStringHead___lam__0___closed__5));
v___y_237_ = v___x_268_;
v___y_238_ = v___x_269_;
v___y_239_ = v___x_273_;
goto v___jp_236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_instEncodeV11Head___lam__0___boxed(lean_object* v_buffer_314_, lean_object* v_req_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Std_Http_Request_instEncodeV11Head___lam__0(v_buffer_314_, v_req_315_);
lean_dec_ref(v_req_315_);
return v_res_316_;
}
}
static lean_object* _init_l_Std_Http_Request_new___closed__2(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = l_Std_Http_Extensions_empty;
v___x_325_ = ((lean_object*)(l_Std_Http_Request_new___closed__1));
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_324_);
return v___x_326_;
}
}
static lean_object* _init_l_Std_Http_Request_new(void){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = lean_obj_once(&l_Std_Http_Request_new___closed__2, &l_Std_Http_Request_new___closed__2_once, _init_l_Std_Http_Request_new___closed__2);
return v___x_327_;
}
}
static lean_object* _init_l_Std_Http_Request_Builder_empty(void){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_obj_once(&l_Std_Http_Request_new___closed__2, &l_Std_Http_Request_new___closed__2_once, _init_l_Std_Http_Request_new___closed__2);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method(lean_object* v_builder_329_, uint8_t v_method_330_){
_start:
{
lean_object* v_line_331_; lean_object* v_extensions_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_348_; 
v_line_331_ = lean_ctor_get(v_builder_329_, 0);
v_extensions_332_ = lean_ctor_get(v_builder_329_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v_builder_329_);
if (v_isSharedCheck_348_ == 0)
{
v___x_334_ = v_builder_329_;
v_isShared_335_ = v_isSharedCheck_348_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_extensions_332_);
lean_inc(v_line_331_);
lean_dec(v_builder_329_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_348_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
uint8_t v_version_336_; lean_object* v_uri_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_347_; 
v_version_336_ = lean_ctor_get_uint8(v_line_331_, sizeof(void*)*1 + 1);
v_uri_337_ = lean_ctor_get(v_line_331_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v_line_331_);
if (v_isSharedCheck_347_ == 0)
{
v___x_339_ = v_line_331_;
v_isShared_340_ = v_isSharedCheck_347_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_uri_337_);
lean_dec(v_line_331_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_347_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_uri_337_);
lean_ctor_set_uint8(v_reuseFailAlloc_346_, sizeof(void*)*1 + 1, v_version_336_);
v___x_342_ = v_reuseFailAlloc_346_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_344_; 
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*1, v_method_330_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_342_);
v___x_344_ = v___x_334_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_extensions_332_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_method___boxed(lean_object* v_builder_349_, lean_object* v_method_350_){
_start:
{
uint8_t v_method_boxed_351_; lean_object* v_res_352_; 
v_method_boxed_351_ = lean_unbox(v_method_350_);
v_res_352_ = l_Std_Http_Request_Builder_method(v_builder_349_, v_method_boxed_351_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version(lean_object* v_builder_353_, uint8_t v_version_354_){
_start:
{
lean_object* v_line_355_; lean_object* v_extensions_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_372_; 
v_line_355_ = lean_ctor_get(v_builder_353_, 0);
v_extensions_356_ = lean_ctor_get(v_builder_353_, 1);
v_isSharedCheck_372_ = !lean_is_exclusive(v_builder_353_);
if (v_isSharedCheck_372_ == 0)
{
v___x_358_ = v_builder_353_;
v_isShared_359_ = v_isSharedCheck_372_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_extensions_356_);
lean_inc(v_line_355_);
lean_dec(v_builder_353_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_372_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
uint8_t v_method_360_; lean_object* v_uri_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_371_; 
v_method_360_ = lean_ctor_get_uint8(v_line_355_, sizeof(void*)*1);
v_uri_361_ = lean_ctor_get(v_line_355_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v_line_355_);
if (v_isSharedCheck_371_ == 0)
{
v___x_363_ = v_line_355_;
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_uri_361_);
lean_dec(v_line_355_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_uri_361_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, sizeof(void*)*1, v_method_360_);
v___x_366_ = v_reuseFailAlloc_370_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_368_; 
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*1 + 1, v_version_354_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_366_);
v___x_368_ = v___x_358_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_extensions_356_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_version___boxed(lean_object* v_builder_373_, lean_object* v_version_374_){
_start:
{
uint8_t v_version_boxed_375_; lean_object* v_res_376_; 
v_version_boxed_375_ = lean_unbox(v_version_374_);
v_res_376_ = l_Std_Http_Request_Builder_version(v_builder_373_, v_version_boxed_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_uri(lean_object* v_builder_377_, lean_object* v_uri_378_){
_start:
{
lean_object* v_line_379_; lean_object* v_extensions_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_397_; 
v_line_379_ = lean_ctor_get(v_builder_377_, 0);
v_extensions_380_ = lean_ctor_get(v_builder_377_, 1);
v_isSharedCheck_397_ = !lean_is_exclusive(v_builder_377_);
if (v_isSharedCheck_397_ == 0)
{
v___x_382_ = v_builder_377_;
v_isShared_383_ = v_isSharedCheck_397_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_extensions_380_);
lean_inc(v_line_379_);
lean_dec(v_builder_377_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_397_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
uint8_t v_method_384_; uint8_t v_version_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_395_; 
v_method_384_ = lean_ctor_get_uint8(v_line_379_, sizeof(void*)*1);
v_version_385_ = lean_ctor_get_uint8(v_line_379_, sizeof(void*)*1 + 1);
v_isSharedCheck_395_ = !lean_is_exclusive(v_line_379_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; 
v_unused_396_ = lean_ctor_get(v_line_379_, 0);
lean_dec(v_unused_396_);
v___x_387_ = v_line_379_;
v_isShared_388_ = v_isSharedCheck_395_;
goto v_resetjp_386_;
}
else
{
lean_dec(v_line_379_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_395_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v_uri_378_);
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_uri_378_);
lean_ctor_set_uint8(v_reuseFailAlloc_394_, sizeof(void*)*1, v_method_384_);
lean_ctor_set_uint8(v_reuseFailAlloc_394_, sizeof(void*)*1 + 1, v_version_385_);
v___x_390_ = v_reuseFailAlloc_394_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_392_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_390_);
v___x_392_ = v___x_382_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_extensions_380_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension___redArg(lean_object* v_builder_399_, lean_object* v_inst_400_, lean_object* v_data_401_){
_start:
{
lean_object* v_line_402_; lean_object* v_extensions_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_414_; 
v_line_402_ = lean_ctor_get(v_builder_399_, 0);
v_extensions_403_ = lean_ctor_get(v_builder_399_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_builder_399_);
if (v_isSharedCheck_414_ == 0)
{
v___x_405_ = v_builder_399_;
v_isShared_406_ = v_isSharedCheck_414_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_extensions_403_);
lean_inc(v_line_402_);
lean_dec(v_builder_399_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_414_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v_dyn_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
v_dyn_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_407_, 0, v_inst_400_);
lean_ctor_set(v_dyn_407_, 1, v_data_401_);
v___x_408_ = ((lean_object*)(l_Std_Http_Request_Builder_extension___redArg___closed__0));
v___x_409_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_407_);
v___x_410_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_408_, v___x_409_, v_dyn_407_, v_extensions_403_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v___x_410_);
v___x_412_ = v___x_405_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_line_402_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_extension(lean_object* v_00_u03b1_415_, lean_object* v_builder_416_, lean_object* v_inst_417_, lean_object* v_data_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_Http_Request_Builder_extension___redArg(v_builder_416_, v_inst_417_, v_data_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg(lean_object* v_builder_420_, lean_object* v_body_421_){
_start:
{
lean_object* v_line_422_; lean_object* v_extensions_423_; lean_object* v___x_424_; 
v_line_422_ = lean_ctor_get(v_builder_420_, 0);
v_extensions_423_ = lean_ctor_get(v_builder_420_, 1);
lean_inc(v_extensions_423_);
lean_inc_ref(v_line_422_);
v___x_424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_424_, 0, v_line_422_);
lean_ctor_set(v___x_424_, 1, v_body_421_);
lean_ctor_set(v___x_424_, 2, v_extensions_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___redArg___boxed(lean_object* v_builder_425_, lean_object* v_body_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_Http_Request_Builder_body___redArg(v_builder_425_, v_body_426_);
lean_dec_ref(v_builder_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body(lean_object* v_t_428_, lean_object* v_builder_429_, lean_object* v_body_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Std_Http_Request_Builder_body___redArg(v_builder_429_, v_body_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_Builder_body___boxed(lean_object* v_t_432_, lean_object* v_builder_433_, lean_object* v_body_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Std_Http_Request_Builder_body(v_t_432_, v_builder_433_, v_body_434_);
lean_dec_ref(v_builder_433_);
return v_res_435_;
}
}
static lean_object* _init_l_Std_Http_Request_get___closed__0(void){
_start:
{
uint8_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = 8;
v___x_437_ = l_Std_Http_Request_new;
v___x_438_ = l_Std_Http_Request_Builder_method(v___x_437_, v___x_436_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_get(lean_object* v_uri_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_obj_once(&l_Std_Http_Request_get___closed__0, &l_Std_Http_Request_get___closed__0_once, _init_l_Std_Http_Request_get___closed__0);
v___x_441_ = l_Std_Http_Request_Builder_uri(v___x_440_, v_uri_439_);
return v___x_441_;
}
}
static lean_object* _init_l_Std_Http_Request_post___closed__0(void){
_start:
{
uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = 23;
v___x_443_ = l_Std_Http_Request_new;
v___x_444_ = l_Std_Http_Request_Builder_method(v___x_443_, v___x_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_post(lean_object* v_uri_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_obj_once(&l_Std_Http_Request_post___closed__0, &l_Std_Http_Request_post___closed__0_once, _init_l_Std_Http_Request_post___closed__0);
v___x_447_ = l_Std_Http_Request_Builder_uri(v___x_446_, v_uri_445_);
return v___x_447_;
}
}
static lean_object* _init_l_Std_Http_Request_put___closed__0(void){
_start:
{
uint8_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_448_ = 27;
v___x_449_ = l_Std_Http_Request_new;
v___x_450_ = l_Std_Http_Request_Builder_method(v___x_449_, v___x_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_put(lean_object* v_uri_451_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_obj_once(&l_Std_Http_Request_put___closed__0, &l_Std_Http_Request_put___closed__0_once, _init_l_Std_Http_Request_put___closed__0);
v___x_453_ = l_Std_Http_Request_Builder_uri(v___x_452_, v_uri_451_);
return v___x_453_;
}
}
static lean_object* _init_l_Std_Http_Request_delete___closed__0(void){
_start:
{
uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = 7;
v___x_455_ = l_Std_Http_Request_new;
v___x_456_ = l_Std_Http_Request_Builder_method(v___x_455_, v___x_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_delete(lean_object* v_uri_457_){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_obj_once(&l_Std_Http_Request_delete___closed__0, &l_Std_Http_Request_delete___closed__0_once, _init_l_Std_Http_Request_delete___closed__0);
v___x_459_ = l_Std_Http_Request_Builder_uri(v___x_458_, v_uri_457_);
return v___x_459_;
}
}
static lean_object* _init_l_Std_Http_Request_patch___closed__0(void){
_start:
{
uint8_t v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = 22;
v___x_461_ = l_Std_Http_Request_new;
v___x_462_ = l_Std_Http_Request_Builder_method(v___x_461_, v___x_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_patch(lean_object* v_uri_463_){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_obj_once(&l_Std_Http_Request_patch___closed__0, &l_Std_Http_Request_patch___closed__0_once, _init_l_Std_Http_Request_patch___closed__0);
v___x_465_ = l_Std_Http_Request_Builder_uri(v___x_464_, v_uri_463_);
return v___x_465_;
}
}
static lean_object* _init_l_Std_Http_Request_head___closed__0(void){
_start:
{
uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = 9;
v___x_467_ = l_Std_Http_Request_new;
v___x_468_ = l_Std_Http_Request_Builder_method(v___x_467_, v___x_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_head(lean_object* v_uri_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_obj_once(&l_Std_Http_Request_head___closed__0, &l_Std_Http_Request_head___closed__0_once, _init_l_Std_Http_Request_head___closed__0);
v___x_471_ = l_Std_Http_Request_Builder_uri(v___x_470_, v_uri_469_);
return v___x_471_;
}
}
static lean_object* _init_l_Std_Http_Request_options___closed__0(void){
_start:
{
uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = 20;
v___x_473_ = l_Std_Http_Request_new;
v___x_474_ = l_Std_Http_Request_Builder_method(v___x_473_, v___x_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_options(lean_object* v_uri_475_){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_obj_once(&l_Std_Http_Request_options___closed__0, &l_Std_Http_Request_options___closed__0_once, _init_l_Std_Http_Request_options___closed__0);
v___x_477_ = l_Std_Http_Request_Builder_uri(v___x_476_, v_uri_475_);
return v___x_477_;
}
}
static lean_object* _init_l_Std_Http_Request_connect___closed__0(void){
_start:
{
uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = 5;
v___x_479_ = l_Std_Http_Request_new;
v___x_480_ = l_Std_Http_Request_Builder_method(v___x_479_, v___x_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_connect(lean_object* v_uri_481_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_obj_once(&l_Std_Http_Request_connect___closed__0, &l_Std_Http_Request_connect___closed__0_once, _init_l_Std_Http_Request_connect___closed__0);
v___x_483_ = l_Std_Http_Request_Builder_uri(v___x_482_, v_uri_481_);
return v___x_483_;
}
}
static lean_object* _init_l_Std_Http_Request_trace___closed__0(void){
_start:
{
uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = 32;
v___x_485_ = l_Std_Http_Request_new;
v___x_486_ = l_Std_Http_Request_Builder_method(v___x_485_, v___x_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Request_trace(lean_object* v_uri_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_obj_once(&l_Std_Http_Request_trace___closed__0, &l_Std_Http_Request_trace___closed__0_once, _init_l_Std_Http_Request_trace___closed__0);
v___x_489_ = l_Std_Http_Request_Builder_uri(v___x_488_, v_uri_487_);
return v___x_489_;
}
}
lean_object* runtime_initialize_Std_Internal_Http_Data_Extensions(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Method(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Version(uint8_t builtin);
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
