// Lean compiler output
// Module: Std.Internal.Http.Data.Response
// Imports: public import Std.Internal.Http.Data.Extensions public import Std.Internal.Http.Data.Status public import Std.Internal.Http.Data.Version
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
extern lean_object* l_Std_Http_instInhabitedExtensions_default;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Http_Extensions_compareName___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint16_t l_Std_Http_Status_toCode(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_Http_Status_reasonPhrase(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
extern lean_object* l_Std_Http_Extensions_empty;
lean_object* l_Std_Http_instReprStatus_repr(lean_object*, lean_object*);
lean_object* l_Std_Http_instReprVersion_repr(uint8_t, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
static const lean_ctor_object l_Std_Http_Response_instInhabitedHead_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_Response_instInhabitedHead_default___closed__0 = (const lean_object*)&l_Std_Http_Response_instInhabitedHead_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Response_instInhabitedHead_default = (const lean_object*)&l_Std_Http_Response_instInhabitedHead_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Response_instInhabitedHead = (const lean_object*)&l_Std_Http_Response_instInhabitedHead_default___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Response_instReprHead_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Response_instReprHead_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Http_Response_instReprHead_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "status"};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Http_Response_instReprHead_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__4 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__3_value),((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__6 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Http_Response_instReprHead_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__7;
static const lean_string_object l_Std_Http_Response_instReprHead_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__8 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__9 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Http_Response_instReprHead_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__10 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__11 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__11_value;
static lean_once_cell_t l_Std_Http_Response_instReprHead_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__12;
static const lean_string_object l_Std_Http_Response_instReprHead_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__13 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__13_value;
static lean_once_cell_t l_Std_Http_Response_instReprHead_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__14;
static lean_once_cell_t l_Std_Http_Response_instReprHead_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__15;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__16 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__16_value;
static const lean_ctor_object l_Std_Http_Response_instReprHead_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__13_value)}};
static const lean_object* l_Std_Http_Response_instReprHead_repr___redArg___closed__17 = (const lean_object*)&l_Std_Http_Response_instReprHead_repr___redArg___closed__17_value;
LEAN_EXPORT lean_object* l_Std_Http_Response_instReprHead_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_instReprHead_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_instReprHead_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Response_instReprHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Response_instReprHead_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instReprHead___closed__0 = (const lean_object*)&l_Std_Http_Response_instReprHead___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Response_instReprHead = (const lean_object*)&l_Std_Http_Response_instReprHead___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__0___closed__0_value;
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__0___closed__1_value;
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.0"};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__0___closed__2 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__0___closed__2_value;
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.1"};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__0___closed__3 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__0___closed__3_value;
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/2.0"};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__0___closed__4 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__0___closed__4_value;
static const lean_string_object l_Std_Http_Response_instToStringHead___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/3.0"};
static const lean_object* l_Std_Http_Response_instToStringHead___lam__0___closed__5 = (const lean_object*)&l_Std_Http_Response_instToStringHead___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_Response_instToStringHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Response_instToStringHead___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instToStringHead___closed__0 = (const lean_object*)&l_Std_Http_Response_instToStringHead___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Response_instToStringHead = (const lean_object*)&l_Std_Http_Response_instToStringHead___closed__0_value;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__2;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3;
static lean_once_cell_t l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Response_instEncodeV11Head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Response_instEncodeV11Head___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_instEncodeV11Head___closed__0 = (const lean_object*)&l_Std_Http_Response_instEncodeV11Head___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Response_instEncodeV11Head = (const lean_object*)&l_Std_Http_Response_instEncodeV11Head___closed__0_value;
static const lean_ctor_object l_Std_Http_Response_new___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_Response_new___closed__0 = (const lean_object*)&l_Std_Http_Response_new___closed__0_value;
static lean_once_cell_t l_Std_Http_Response_new___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_new___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_Response_new;
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_empty;
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_status(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Response_Builder_extension___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Extensions_compareName___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Response_Builder_extension___redArg___closed__0 = (const lean_object*)&l_Std_Http_Response_Builder_extension___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Response_ok___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_ok___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_ok;
LEAN_EXPORT lean_object* l_Std_Http_Response_withStatus(lean_object*);
static lean_once_cell_t l_Std_Http_Response_notFound___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_notFound___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_notFound;
static lean_once_cell_t l_Std_Http_Response_internalServerError___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_internalServerError___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_internalServerError;
static lean_once_cell_t l_Std_Http_Response_badRequest___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_badRequest___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_badRequest;
static lean_once_cell_t l_Std_Http_Response_created___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_created___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_created;
static lean_once_cell_t l_Std_Http_Response_accepted___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_accepted___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_accepted;
static lean_once_cell_t l_Std_Http_Response_unauthorized___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_unauthorized___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_unauthorized;
static lean_once_cell_t l_Std_Http_Response_forbidden___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_forbidden___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_forbidden;
static lean_once_cell_t l_Std_Http_Response_conflict___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_conflict___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_conflict;
static lean_once_cell_t l_Std_Http_Response_serviceUnavailable___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Response_serviceUnavailable___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Response_serviceUnavailable;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Response_instReprHead_repr_spec__0(lean_object* v_a_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_nat_to_int(v_a_6_);
return v___x_7_;
}
}
static lean_object* _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_unsigned_to_nat(10u);
v___x_22_ = lean_nat_to_int(v___x_21_);
return v___x_22_;
}
}
static lean_object* _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_unsigned_to_nat(11u);
v___x_30_ = lean_nat_to_int(v___x_29_);
return v___x_30_;
}
}
static lean_object* _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = ((lean_object*)(l_Std_Http_Response_instReprHead_repr___redArg___closed__0));
v___x_33_ = lean_string_length(v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_obj_once(&l_Std_Http_Response_instReprHead_repr___redArg___closed__14, &l_Std_Http_Response_instReprHead_repr___redArg___closed__14_once, _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__14);
v___x_35_ = lean_nat_to_int(v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instReprHead_repr___redArg(lean_object* v_x_40_){
_start:
{
lean_object* v_status_41_; uint8_t v_version_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_76_; 
v_status_41_ = lean_ctor_get(v_x_40_, 0);
v_version_42_ = lean_ctor_get_uint8(v_x_40_, sizeof(void*)*1);
v_isSharedCheck_76_ = !lean_is_exclusive(v_x_40_);
if (v_isSharedCheck_76_ == 0)
{
v___x_44_ = v_x_40_;
v_isShared_45_ = v_isSharedCheck_76_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_status_41_);
lean_dec(v_x_40_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_76_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; lean_object* v___x_54_; 
v___x_46_ = ((lean_object*)(l_Std_Http_Response_instReprHead_repr___redArg___closed__5));
v___x_47_ = ((lean_object*)(l_Std_Http_Response_instReprHead_repr___redArg___closed__6));
v___x_48_ = lean_obj_once(&l_Std_Http_Response_instReprHead_repr___redArg___closed__7, &l_Std_Http_Response_instReprHead_repr___redArg___closed__7_once, _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__7);
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = l_Std_Http_instReprStatus_repr(v_status_41_, v___x_49_);
v___x_51_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_48_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
v___x_52_ = 0;
if (v_isShared_45_ == 0)
{
lean_ctor_set_tag(v___x_44_, 6);
lean_ctor_set(v___x_44_, 0, v___x_51_);
v___x_54_ = v___x_44_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_51_);
v___x_54_ = v_reuseFailAlloc_75_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
lean_ctor_set_uint8(v___x_54_, sizeof(void*)*1, v___x_52_);
v___x_55_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_47_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = ((lean_object*)(l_Std_Http_Response_instReprHead_repr___redArg___closed__9));
v___x_57_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___x_58_ = lean_box(1);
v___x_59_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_57_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
v___x_60_ = ((lean_object*)(l_Std_Http_Response_instReprHead_repr___redArg___closed__11));
v___x_61_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_59_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_46_);
v___x_63_ = lean_obj_once(&l_Std_Http_Response_instReprHead_repr___redArg___closed__12, &l_Std_Http_Response_instReprHead_repr___redArg___closed__12_once, _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__12);
v___x_64_ = l_Std_Http_instReprVersion_repr(v_version_42_, v___x_49_);
v___x_65_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
v___x_66_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set_uint8(v___x_66_, sizeof(void*)*1, v___x_52_);
v___x_67_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_62_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = lean_obj_once(&l_Std_Http_Response_instReprHead_repr___redArg___closed__15, &l_Std_Http_Response_instReprHead_repr___redArg___closed__15_once, _init_l_Std_Http_Response_instReprHead_repr___redArg___closed__15);
v___x_69_ = ((lean_object*)(l_Std_Http_Response_instReprHead_repr___redArg___closed__16));
v___x_70_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___x_67_);
v___x_71_ = ((lean_object*)(l_Std_Http_Response_instReprHead_repr___redArg___closed__17));
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_68_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set_uint8(v___x_74_, sizeof(void*)*1, v___x_52_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instReprHead_repr(lean_object* v_x_77_, lean_object* v_prec_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Std_Http_Response_instReprHead_repr___redArg(v_x_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instReprHead_repr___boxed(lean_object* v_x_80_, lean_object* v_prec_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_Http_Response_instReprHead_repr(v_x_80_, v_prec_81_);
lean_dec(v_prec_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse_default___redArg(lean_object* v_inst_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = ((lean_object*)(l_Std_Http_Response_instInhabitedHead_default));
v___x_87_ = l_Std_Http_instInhabitedExtensions_default;
v___x_88_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set(v___x_88_, 1, v_inst_85_);
lean_ctor_set(v___x_88_, 2, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse_default(lean_object* v_a_89_, lean_object* v_inst_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Std_Http_instInhabitedResponse_default___redArg(v_inst_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse___redArg(lean_object* v_inst_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Std_Http_instInhabitedResponse_default___redArg(v_inst_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedResponse(lean_object* v_a_94_, lean_object* v_inst_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Std_Http_instInhabitedResponse_default___redArg(v_inst_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__0(lean_object* v_r_103_){
_start:
{
lean_object* v_status_104_; uint8_t v_version_105_; lean_object* v___y_107_; 
v_status_104_ = lean_ctor_get(v_r_103_, 0);
v_version_105_ = lean_ctor_get_uint8(v_r_103_, sizeof(void*)*1);
switch(v_version_105_)
{
case 0:
{
lean_object* v___x_119_; 
v___x_119_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__0___closed__2));
v___y_107_ = v___x_119_;
goto v___jp_106_;
}
case 1:
{
lean_object* v___x_120_; 
v___x_120_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__0___closed__3));
v___y_107_ = v___x_120_;
goto v___jp_106_;
}
case 2:
{
lean_object* v___x_121_; 
v___x_121_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__0___closed__4));
v___y_107_ = v___x_121_;
goto v___jp_106_;
}
default: 
{
lean_object* v___x_122_; 
v___x_122_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__0___closed__5));
v___y_107_ = v___x_122_;
goto v___jp_106_;
}
}
v___jp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint16_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_108_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__0___closed__0));
v___x_109_ = lean_string_append(v___y_107_, v___x_108_);
v___x_110_ = l_Std_Http_Status_toCode(v_status_104_);
v___x_111_ = lean_uint16_to_nat(v___x_110_);
v___x_112_ = l_Nat_reprFast(v___x_111_);
v___x_113_ = lean_string_append(v___x_109_, v___x_112_);
lean_dec_ref(v___x_112_);
v___x_114_ = lean_string_append(v___x_113_, v___x_108_);
v___x_115_ = l_Std_Http_Status_reasonPhrase(v_status_104_);
v___x_116_ = lean_string_append(v___x_114_, v___x_115_);
lean_dec_ref(v___x_115_);
v___x_117_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__0___closed__1));
v___x_118_ = lean_string_append(v___x_116_, v___x_117_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instToStringHead___lam__0___boxed(lean_object* v_r_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Std_Http_Response_instToStringHead___lam__0(v_r_123_);
lean_dec_ref(v_r_123_);
return v_res_124_;
}
}
static uint8_t _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0(void){
_start:
{
uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = 32;
v___x_128_ = lean_uint32_to_uint8(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1(void){
_start:
{
uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_129_ = lean_uint8_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__0);
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lean_mk_empty_array_with_capacity(v___x_130_);
v___x_132_ = lean_box(v___x_129_);
v___x_133_ = lean_array_push(v___x_131_, v___x_132_);
v___x_134_ = lean_byte_array_mk(v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__2(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1);
v___x_136_ = lean_byte_array_size(v___x_135_);
return v___x_136_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__0___closed__1));
v___x_138_ = lean_string_to_utf8(v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3);
v___x_140_ = lean_byte_array_size(v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0(lean_object* v_buffer_141_, lean_object* v_r_142_){
_start:
{
lean_object* v_status_143_; uint8_t v_version_144_; lean_object* v___y_146_; 
v_status_143_ = lean_ctor_get(v_r_142_, 0);
v_version_144_ = lean_ctor_get_uint8(v_r_142_, sizeof(void*)*1);
switch(v_version_144_)
{
case 0:
{
lean_object* v___x_182_; 
v___x_182_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__0___closed__2));
v___y_146_ = v___x_182_;
goto v___jp_145_;
}
case 1:
{
lean_object* v___x_183_; 
v___x_183_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__0___closed__3));
v___y_146_ = v___x_183_;
goto v___jp_145_;
}
case 2:
{
lean_object* v___x_184_; 
v___x_184_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__0___closed__4));
v___y_146_ = v___x_184_;
goto v___jp_145_;
}
default: 
{
lean_object* v___x_185_; 
v___x_185_ = ((lean_object*)(l_Std_Http_Response_instToStringHead___lam__0___closed__5));
v___y_146_ = v___x_185_;
goto v___jp_145_;
}
}
v___jp_145_:
{
lean_object* v_data_147_; lean_object* v_size_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_181_; 
v_data_147_ = lean_ctor_get(v_buffer_141_, 0);
v_size_148_ = lean_ctor_get(v_buffer_141_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v_buffer_141_);
if (v_isSharedCheck_181_ == 0)
{
v___x_150_ = v_buffer_141_;
v_isShared_151_ = v_isSharedCheck_181_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_size_148_);
lean_inc(v_data_147_);
lean_dec(v_buffer_141_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_181_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint16_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_152_ = lean_string_to_utf8(v___y_146_);
lean_dec_ref(v___y_146_);
lean_inc_ref(v___x_152_);
v___x_153_ = lean_array_push(v_data_147_, v___x_152_);
v___x_154_ = lean_byte_array_size(v___x_152_);
lean_dec_ref(v___x_152_);
v___x_155_ = lean_nat_add(v_size_148_, v___x_154_);
lean_dec(v_size_148_);
v___x_156_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__1);
v___x_157_ = lean_array_push(v___x_153_, v___x_156_);
v___x_158_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__2, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__2_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__2);
v___x_159_ = lean_nat_add(v___x_155_, v___x_158_);
lean_dec(v___x_155_);
v___x_160_ = l_Std_Http_Status_toCode(v_status_143_);
v___x_161_ = lean_uint16_to_nat(v___x_160_);
v___x_162_ = l_Nat_reprFast(v___x_161_);
v___x_163_ = lean_string_to_utf8(v___x_162_);
lean_dec_ref(v___x_162_);
lean_inc_ref(v___x_163_);
v___x_164_ = lean_array_push(v___x_157_, v___x_163_);
v___x_165_ = lean_byte_array_size(v___x_163_);
lean_dec_ref(v___x_163_);
v___x_166_ = lean_nat_add(v___x_159_, v___x_165_);
lean_dec(v___x_159_);
v___x_167_ = lean_array_push(v___x_164_, v___x_156_);
v___x_168_ = lean_nat_add(v___x_166_, v___x_158_);
lean_dec(v___x_166_);
v___x_169_ = l_Std_Http_Status_reasonPhrase(v_status_143_);
v___x_170_ = lean_string_to_utf8(v___x_169_);
lean_dec_ref(v___x_169_);
lean_inc_ref(v___x_170_);
v___x_171_ = lean_array_push(v___x_167_, v___x_170_);
v___x_172_ = lean_byte_array_size(v___x_170_);
lean_dec_ref(v___x_170_);
v___x_173_ = lean_nat_add(v___x_168_, v___x_172_);
lean_dec(v___x_168_);
v___x_174_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__3);
v___x_175_ = lean_array_push(v___x_171_, v___x_174_);
v___x_176_ = lean_obj_once(&l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4, &l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4_once, _init_l_Std_Http_Response_instEncodeV11Head___lam__0___closed__4);
v___x_177_ = lean_nat_add(v___x_173_, v___x_176_);
lean_dec(v___x_173_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v___x_177_);
lean_ctor_set(v___x_150_, 0, v___x_175_);
v___x_179_ = v___x_150_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_instEncodeV11Head___lam__0___boxed(lean_object* v_buffer_186_, lean_object* v_r_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_Http_Response_instEncodeV11Head___lam__0(v_buffer_186_, v_r_187_);
lean_dec_ref(v_r_187_);
return v_res_188_;
}
}
static lean_object* _init_l_Std_Http_Response_new___closed__1(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = l_Std_Http_Extensions_empty;
v___x_195_ = ((lean_object*)(l_Std_Http_Response_new___closed__0));
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_194_);
return v___x_196_;
}
}
static lean_object* _init_l_Std_Http_Response_new(void){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_obj_once(&l_Std_Http_Response_new___closed__1, &l_Std_Http_Response_new___closed__1_once, _init_l_Std_Http_Response_new___closed__1);
return v___x_197_;
}
}
static lean_object* _init_l_Std_Http_Response_Builder_empty(void){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_obj_once(&l_Std_Http_Response_new___closed__1, &l_Std_Http_Response_new___closed__1_once, _init_l_Std_Http_Response_new___closed__1);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_status(lean_object* v_builder_199_, lean_object* v_status_200_){
_start:
{
lean_object* v_line_201_; lean_object* v_extensions_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_218_; 
v_line_201_ = lean_ctor_get(v_builder_199_, 0);
v_extensions_202_ = lean_ctor_get(v_builder_199_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v_builder_199_);
if (v_isSharedCheck_218_ == 0)
{
v___x_204_ = v_builder_199_;
v_isShared_205_ = v_isSharedCheck_218_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_extensions_202_);
lean_inc(v_line_201_);
lean_dec(v_builder_199_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_218_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
uint8_t v_version_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_216_; 
v_version_206_ = lean_ctor_get_uint8(v_line_201_, sizeof(void*)*1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_line_201_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; 
v_unused_217_ = lean_ctor_get(v_line_201_, 0);
lean_dec(v_unused_217_);
v___x_208_ = v_line_201_;
v_isShared_209_ = v_isSharedCheck_216_;
goto v_resetjp_207_;
}
else
{
lean_dec(v_line_201_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_216_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v_status_200_);
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_status_200_);
lean_ctor_set_uint8(v_reuseFailAlloc_215_, sizeof(void*)*1, v_version_206_);
v___x_211_ = v_reuseFailAlloc_215_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_213_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_211_);
v___x_213_ = v___x_204_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_extensions_202_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension___redArg(lean_object* v_builder_220_, lean_object* v_inst_221_, lean_object* v_data_222_){
_start:
{
lean_object* v_line_223_; lean_object* v_extensions_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_235_; 
v_line_223_ = lean_ctor_get(v_builder_220_, 0);
v_extensions_224_ = lean_ctor_get(v_builder_220_, 1);
v_isSharedCheck_235_ = !lean_is_exclusive(v_builder_220_);
if (v_isSharedCheck_235_ == 0)
{
v___x_226_ = v_builder_220_;
v_isShared_227_ = v_isSharedCheck_235_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_extensions_224_);
lean_inc(v_line_223_);
lean_dec(v_builder_220_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_235_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v_dyn_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v_dyn_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_dyn_228_, 0, v_inst_221_);
lean_ctor_set(v_dyn_228_, 1, v_data_222_);
v___x_229_ = ((lean_object*)(l_Std_Http_Response_Builder_extension___redArg___closed__0));
v___x_230_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_228_);
v___x_231_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_229_, v___x_230_, v_dyn_228_, v_extensions_224_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_231_);
v___x_233_ = v___x_226_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_line_223_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_extension(lean_object* v_00_u03b1_236_, lean_object* v_builder_237_, lean_object* v_inst_238_, lean_object* v_data_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Std_Http_Response_Builder_extension___redArg(v_builder_237_, v_inst_238_, v_data_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg(lean_object* v_builder_241_, lean_object* v_body_242_){
_start:
{
lean_object* v_line_243_; lean_object* v_extensions_244_; lean_object* v___x_245_; 
v_line_243_ = lean_ctor_get(v_builder_241_, 0);
v_extensions_244_ = lean_ctor_get(v_builder_241_, 1);
lean_inc(v_extensions_244_);
lean_inc_ref(v_line_243_);
v___x_245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_245_, 0, v_line_243_);
lean_ctor_set(v___x_245_, 1, v_body_242_);
lean_ctor_set(v___x_245_, 2, v_extensions_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___redArg___boxed(lean_object* v_builder_246_, lean_object* v_body_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Std_Http_Response_Builder_body___redArg(v_builder_246_, v_body_247_);
lean_dec_ref(v_builder_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body(lean_object* v_t_249_, lean_object* v_builder_250_, lean_object* v_body_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Std_Http_Response_Builder_body___redArg(v_builder_250_, v_body_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_body___boxed(lean_object* v_t_253_, lean_object* v_builder_254_, lean_object* v_body_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Std_Http_Response_Builder_body(v_t_253_, v_builder_254_, v_body_255_);
lean_dec_ref(v_builder_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg(lean_object* v_inst_257_, lean_object* v_builder_258_){
_start:
{
lean_object* v_line_259_; lean_object* v_extensions_260_; lean_object* v___x_261_; 
v_line_259_ = lean_ctor_get(v_builder_258_, 0);
v_extensions_260_ = lean_ctor_get(v_builder_258_, 1);
lean_inc(v_extensions_260_);
lean_inc_ref(v_line_259_);
v___x_261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_261_, 0, v_line_259_);
lean_ctor_set(v___x_261_, 1, v_inst_257_);
lean_ctor_set(v___x_261_, 2, v_extensions_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___redArg___boxed(lean_object* v_inst_262_, lean_object* v_builder_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Std_Http_Response_Builder_build___redArg(v_inst_262_, v_builder_263_);
lean_dec_ref(v_builder_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build(lean_object* v_t_265_, lean_object* v_inst_266_, lean_object* v_builder_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Std_Http_Response_Builder_build___redArg(v_inst_266_, v_builder_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_Builder_build___boxed(lean_object* v_t_269_, lean_object* v_inst_270_, lean_object* v_builder_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Std_Http_Response_Builder_build(v_t_269_, v_inst_270_, v_builder_271_);
lean_dec_ref(v_builder_271_);
return v_res_272_;
}
}
static lean_object* _init_l_Std_Http_Response_ok___closed__0(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_box(4);
v___x_274_ = l_Std_Http_Response_Builder_empty;
v___x_275_ = l_Std_Http_Response_Builder_status(v___x_274_, v___x_273_);
return v___x_275_;
}
}
static lean_object* _init_l_Std_Http_Response_ok(void){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lean_obj_once(&l_Std_Http_Response_ok___closed__0, &l_Std_Http_Response_ok___closed__0_once, _init_l_Std_Http_Response_ok___closed__0);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Response_withStatus(lean_object* v_status_277_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = l_Std_Http_Response_Builder_empty;
v___x_279_ = l_Std_Http_Response_Builder_status(v___x_278_, v_status_277_);
return v___x_279_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound___closed__0(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_box(27);
v___x_281_ = l_Std_Http_Response_Builder_empty;
v___x_282_ = l_Std_Http_Response_Builder_status(v___x_281_, v___x_280_);
return v___x_282_;
}
}
static lean_object* _init_l_Std_Http_Response_notFound(void){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_obj_once(&l_Std_Http_Response_notFound___closed__0, &l_Std_Http_Response_notFound___closed__0_once, _init_l_Std_Http_Response_notFound___closed__0);
return v___x_283_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError___closed__0(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = lean_box(52);
v___x_285_ = l_Std_Http_Response_Builder_empty;
v___x_286_ = l_Std_Http_Response_Builder_status(v___x_285_, v___x_284_);
return v___x_286_;
}
}
static lean_object* _init_l_Std_Http_Response_internalServerError(void){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_obj_once(&l_Std_Http_Response_internalServerError___closed__0, &l_Std_Http_Response_internalServerError___closed__0_once, _init_l_Std_Http_Response_internalServerError___closed__0);
return v___x_287_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest___closed__0(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_box(23);
v___x_289_ = l_Std_Http_Response_Builder_empty;
v___x_290_ = l_Std_Http_Response_Builder_status(v___x_289_, v___x_288_);
return v___x_290_;
}
}
static lean_object* _init_l_Std_Http_Response_badRequest(void){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = lean_obj_once(&l_Std_Http_Response_badRequest___closed__0, &l_Std_Http_Response_badRequest___closed__0_once, _init_l_Std_Http_Response_badRequest___closed__0);
return v___x_291_;
}
}
static lean_object* _init_l_Std_Http_Response_created___closed__0(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_box(5);
v___x_293_ = l_Std_Http_Response_Builder_empty;
v___x_294_ = l_Std_Http_Response_Builder_status(v___x_293_, v___x_292_);
return v___x_294_;
}
}
static lean_object* _init_l_Std_Http_Response_created(void){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = lean_obj_once(&l_Std_Http_Response_created___closed__0, &l_Std_Http_Response_created___closed__0_once, _init_l_Std_Http_Response_created___closed__0);
return v___x_295_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted___closed__0(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_box(6);
v___x_297_ = l_Std_Http_Response_Builder_empty;
v___x_298_ = l_Std_Http_Response_Builder_status(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l_Std_Http_Response_accepted(void){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = lean_obj_once(&l_Std_Http_Response_accepted___closed__0, &l_Std_Http_Response_accepted___closed__0_once, _init_l_Std_Http_Response_accepted___closed__0);
return v___x_299_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized___closed__0(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = lean_box(24);
v___x_301_ = l_Std_Http_Response_Builder_empty;
v___x_302_ = l_Std_Http_Response_Builder_status(v___x_301_, v___x_300_);
return v___x_302_;
}
}
static lean_object* _init_l_Std_Http_Response_unauthorized(void){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = lean_obj_once(&l_Std_Http_Response_unauthorized___closed__0, &l_Std_Http_Response_unauthorized___closed__0_once, _init_l_Std_Http_Response_unauthorized___closed__0);
return v___x_303_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden___closed__0(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_304_ = lean_box(26);
v___x_305_ = l_Std_Http_Response_Builder_empty;
v___x_306_ = l_Std_Http_Response_Builder_status(v___x_305_, v___x_304_);
return v___x_306_;
}
}
static lean_object* _init_l_Std_Http_Response_forbidden(void){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = lean_obj_once(&l_Std_Http_Response_forbidden___closed__0, &l_Std_Http_Response_forbidden___closed__0_once, _init_l_Std_Http_Response_forbidden___closed__0);
return v___x_307_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict___closed__0(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_box(32);
v___x_309_ = l_Std_Http_Response_Builder_empty;
v___x_310_ = l_Std_Http_Response_Builder_status(v___x_309_, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_l_Std_Http_Response_conflict(void){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = lean_obj_once(&l_Std_Http_Response_conflict___closed__0, &l_Std_Http_Response_conflict___closed__0_once, _init_l_Std_Http_Response_conflict___closed__0);
return v___x_311_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable___closed__0(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_box(55);
v___x_313_ = l_Std_Http_Response_Builder_empty;
v___x_314_ = l_Std_Http_Response_Builder_status(v___x_313_, v___x_312_);
return v___x_314_;
}
}
static lean_object* _init_l_Std_Http_Response_serviceUnavailable(void){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = lean_obj_once(&l_Std_Http_Response_serviceUnavailable___closed__0, &l_Std_Http_Response_serviceUnavailable___closed__0_once, _init_l_Std_Http_Response_serviceUnavailable___closed__0);
return v___x_315_;
}
}
lean_object* runtime_initialize_Std_Internal_Http_Data_Extensions(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Status(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Version(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Data_Response(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Http_Data_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Status(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Response_new = _init_l_Std_Http_Response_new();
lean_mark_persistent(l_Std_Http_Response_new);
l_Std_Http_Response_Builder_empty = _init_l_Std_Http_Response_Builder_empty();
lean_mark_persistent(l_Std_Http_Response_Builder_empty);
l_Std_Http_Response_ok = _init_l_Std_Http_Response_ok();
lean_mark_persistent(l_Std_Http_Response_ok);
l_Std_Http_Response_notFound = _init_l_Std_Http_Response_notFound();
lean_mark_persistent(l_Std_Http_Response_notFound);
l_Std_Http_Response_internalServerError = _init_l_Std_Http_Response_internalServerError();
lean_mark_persistent(l_Std_Http_Response_internalServerError);
l_Std_Http_Response_badRequest = _init_l_Std_Http_Response_badRequest();
lean_mark_persistent(l_Std_Http_Response_badRequest);
l_Std_Http_Response_created = _init_l_Std_Http_Response_created();
lean_mark_persistent(l_Std_Http_Response_created);
l_Std_Http_Response_accepted = _init_l_Std_Http_Response_accepted();
lean_mark_persistent(l_Std_Http_Response_accepted);
l_Std_Http_Response_unauthorized = _init_l_Std_Http_Response_unauthorized();
lean_mark_persistent(l_Std_Http_Response_unauthorized);
l_Std_Http_Response_forbidden = _init_l_Std_Http_Response_forbidden();
lean_mark_persistent(l_Std_Http_Response_forbidden);
l_Std_Http_Response_conflict = _init_l_Std_Http_Response_conflict();
lean_mark_persistent(l_Std_Http_Response_conflict);
l_Std_Http_Response_serviceUnavailable = _init_l_Std_Http_Response_serviceUnavailable();
lean_mark_persistent(l_Std_Http_Response_serviceUnavailable);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Data_Response(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Http_Data_Extensions(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Status(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Version(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Data_Response(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Http_Data_Extensions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Status(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Data_Response(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Data_Response(builtin);
}
#ifdef __cplusplus
}
#endif
