// Lean compiler output
// Module: Std.Http.Protocol.H1.Redirect
// Imports: public import Std.Http.Data.Request public import Std.Http.Data.Status public import Std.Http.Data.URI
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
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Http_URI_instReprOrigin_repr___redArg(lean_object*);
lean_object* l_Std_Http_instReprRequestTarget_repr(lean_object*, lean_object*);
lean_object* l_Std_Http_instReprMethod_repr(uint8_t, lean_object*);
lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_Http_Header_Name_ofString_x3f(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Std_Http_Header_Name_host;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Origin_hostHeader(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_proxyAuthorization;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Std_Http_Header_Name_connection;
extern lean_object* l_Std_Http_Header_Name_lastModified;
extern lean_object* l_Std_Http_Header_Name_contentLocation;
extern lean_object* l_Std_Http_Header_Name_contentLanguage;
extern lean_object* l_Std_Http_Header_Name_contentEncoding;
extern lean_object* l_Std_Http_Header_Name_contentLength;
extern lean_object* l_Std_Http_Header_Name_contentType;
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Std_Http_URI_instBEqHost_beq(lean_object*, lean_object*);
uint16_t l_Std_Http_URI_Scheme_defaultPort(lean_object*);
lean_object* l_Std_Http_URI_Parser_parseURIReference(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* l_Std_Http_Header_Connection_parse(lean_object*);
extern lean_object* l_Std_Http_Header_Name_ifModifiedSince;
extern lean_object* l_Std_Http_Header_Name_ifNoneMatch;
uint16_t l_Std_Http_Status_toCode(lean_object*);
uint8_t lean_uint16_dec_le(uint16_t, uint16_t);
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
uint8_t l_Std_Http_instBEqMethod_beq(uint8_t, uint8_t);
uint8_t l_Std_Http_instBEqStatus_beq(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_location;
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_RequestTarget_pathOrRoot(lean_object*);
lean_object* l_Std_Http_URI_Path_normalize(lean_object*);
lean_object* l_Std_Http_URI_Path_parent(lean_object*);
lean_object* l_Std_Http_URI_Path_join(lean_object*, lean_object*);
uint8_t l_Std_Http_URI_Path_isEmpty(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
extern lean_object* l_Std_Http_Header_Name_keepAlive;
extern lean_object* l_Std_Http_Header_Name_referer;
extern lean_object* l_Std_Http_Header_Name_cookie;
extern lean_object* l_Std_Http_Header_Name_authorization;
uint8_t l_Std_Http_URI_instBEqOrigin_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_RedirectBodyAction_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Std.Http.Protocol.H1.RedirectBodyAction.empty"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__1_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Std.Http.Protocol.H1.RedirectBodyAction.replay"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__2_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__2_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__3_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_instReprRedirectBodyAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectBodyAction___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectBodyAction___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction_default;
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Protocol_H1_instReprRedirectPlan_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "origin"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__4 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__3_value),((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__6 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__8 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__9 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "target"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__10 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__11 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__11_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "method"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__12 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__12_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__12_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__13 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__13_value;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "headers"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__14 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__14_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__14_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__15 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__15_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "bodyAction"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__17 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__17_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__17_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__18 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__18_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "isCrossOrigin"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__20 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__20_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__20_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__21 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__21_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22;
static const lean_string_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__23 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__23_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24;
static lean_once_cell_t l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__26 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__26_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__23_value)}};
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__27 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__27_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_instReprRedirectPlan___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan = (const lean_object*)&l_Std_Http_Protocol_H1_instReprRedirectPlan___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_done_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_follow_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_follow_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome_default;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___boxed(lean_object*);
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
static lean_once_cell_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolvedPath(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Protocol_H1_decideRedirect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*9 + 0, .m_other = 9, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(64) << 1) | 1)),((lean_object*)(((size_t)(253) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___closed__0_value;
static const lean_closure_object l_Std_Http_Protocol_H1_decideRedirect___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_decideRedirect___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___closed__0_value)} };
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___closed__1_value;
static const lean_string_object l_Std_Http_Protocol_H1_decideRedirect___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "http"};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___closed__2_value;
static const lean_string_object l_Std_Http_Protocol_H1_decideRedirect___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "https"};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___redArg(lean_object* v_empty_22_){
_start:
{
lean_inc(v_empty_22_);
return v_empty_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___redArg___boxed(lean_object* v_empty_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___redArg(v_empty_23_);
lean_dec(v_empty_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_empty_28_){
_start:
{
lean_inc(v_empty_28_);
return v_empty_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_empty_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Std_Http_Protocol_H1_RedirectBodyAction_empty_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_empty_32_);
lean_dec(v_empty_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___redArg(lean_object* v_replay_35_){
_start:
{
lean_inc(v_replay_35_);
return v_replay_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___redArg___boxed(lean_object* v_replay_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___redArg(v_replay_36_);
lean_dec(v_replay_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_replay_41_){
_start:
{
lean_inc(v_replay_41_);
return v_replay_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_replay_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Std_Http_Protocol_H1_RedirectBodyAction_replay_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_replay_45_);
lean_dec(v_replay_45_);
return v_res_47_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_RedirectBodyAction_ofNat(lean_object* v_n_48_){
_start:
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_nat_dec_le(v_n_48_, v___x_49_);
if (v___x_50_ == 0)
{
uint8_t v___x_51_; 
v___x_51_ = 1;
return v___x_51_;
}
else
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ofNat___boxed(lean_object* v_n_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ofNat(v_n_53_);
lean_dec(v_n_53_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction(uint8_t v_x_56_, uint8_t v_y_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_58_ = lean_box(v_x_56_);
v___x_59_ = lean_obj_tag_nat(v___x_58_);
lean_dec(v___x_58_);
v___x_60_ = lean_box(v_y_57_);
v___x_61_ = lean_obj_tag_nat(v___x_60_);
lean_dec(v___x_60_);
v___x_62_ = lean_nat_dec_eq(v___x_59_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction___boxed(lean_object* v_x_63_, lean_object* v_y_64_){
_start:
{
uint8_t v_x_23__boxed_65_; uint8_t v_y_24__boxed_66_; uint8_t v_res_67_; lean_object* v_r_68_; 
v_x_23__boxed_65_ = lean_unbox(v_x_63_);
v_y_24__boxed_66_ = lean_unbox(v_y_64_);
v_res_67_ = l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction(v_x_23__boxed_65_, v_y_24__boxed_66_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(2u);
v___x_76_ = lean_nat_to_int(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_to_int(v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(uint8_t v_x_79_, lean_object* v_prec_80_){
_start:
{
lean_object* v___y_82_; lean_object* v___y_89_; 
if (v_x_79_ == 0)
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(1024u);
v___x_96_ = lean_nat_dec_le(v___x_95_, v_prec_80_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
v___x_97_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4);
v___y_82_ = v___x_97_;
goto v___jp_81_;
}
else
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5);
v___y_82_ = v___x_98_;
goto v___jp_81_;
}
}
else
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(1024u);
v___x_100_ = lean_nat_dec_le(v___x_99_, v_prec_80_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4);
v___y_89_ = v___x_101_;
goto v___jp_88_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5);
v___y_89_ = v___x_102_;
goto v___jp_88_;
}
}
v___jp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_83_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__1));
lean_inc(v___y_82_);
v___x_84_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_84_, 0, v___y_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = 0;
v___x_86_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_85_);
v___x_87_ = l_Repr_addAppParen(v___x_86_, v_prec_80_);
return v___x_87_;
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_90_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__3));
lean_inc(v___y_89_);
v___x_91_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_91_, 0, v___y_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = 0;
v___x_93_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*1, v___x_92_);
v___x_94_ = l_Repr_addAppParen(v___x_93_, v_prec_80_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___boxed(lean_object* v_x_103_, lean_object* v_prec_104_){
_start:
{
uint8_t v_x_117__boxed_105_; lean_object* v_res_106_; 
v_x_117__boxed_105_ = lean_unbox(v_x_103_);
v_res_106_ = l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(v_x_117__boxed_105_, v_prec_104_);
lean_dec(v_prec_104_);
return v_res_106_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction_default(void){
_start:
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction(void){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = 0;
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Protocol_H1_instReprRedirectPlan_repr_spec__0(lean_object* v_a_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_nat_to_int(v_a_111_);
return v___x_112_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(10u);
v___x_127_ = lean_nat_to_int(v___x_126_);
return v___x_127_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(11u);
v___x_141_ = lean_nat_to_int(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_unsigned_to_nat(14u);
v___x_146_ = lean_nat_to_int(v___x_145_);
return v___x_146_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(17u);
v___x_151_ = lean_nat_to_int(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__0));
v___x_154_ = lean_string_length(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24);
v___x_156_ = lean_nat_to_int(v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg(lean_object* v_x_161_){
_start:
{
lean_object* v_origin_162_; lean_object* v_target_163_; uint8_t v_method_164_; lean_object* v_headers_165_; uint8_t v_bodyAction_166_; uint8_t v_isCrossOrigin_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_origin_162_ = lean_ctor_get(v_x_161_, 0);
lean_inc_ref(v_origin_162_);
v_target_163_ = lean_ctor_get(v_x_161_, 1);
lean_inc(v_target_163_);
v_method_164_ = lean_ctor_get_uint8(v_x_161_, sizeof(void*)*3);
v_headers_165_ = lean_ctor_get(v_x_161_, 2);
lean_inc_ref(v_headers_165_);
v_bodyAction_166_ = lean_ctor_get_uint8(v_x_161_, sizeof(void*)*3 + 1);
v_isCrossOrigin_167_ = lean_ctor_get_uint8(v_x_161_, sizeof(void*)*3 + 2);
lean_dec_ref(v_x_161_);
v___x_168_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__5));
v___x_169_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__6));
v___x_170_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = l_Std_Http_URI_instReprOrigin_repr___redArg(v_origin_162_);
v___x_173_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_170_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = 0;
v___x_175_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_175_, 0, v___x_173_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*1, v___x_174_);
v___x_176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_169_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__9));
v___x_178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = lean_box(1);
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_178_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__11));
v___x_182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_168_);
v___x_184_ = l_Std_Http_instReprRequestTarget_repr(v_target_163_, v___x_171_);
v___x_185_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_170_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*1, v___x_174_);
v___x_187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_183_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_177_);
v___x_189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v___x_179_);
v___x_190_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__13));
v___x_191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_168_);
v___x_193_ = l_Std_Http_instReprMethod_repr(v_method_164_, v___x_171_);
v___x_194_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_170_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*1, v___x_174_);
v___x_196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_192_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_177_);
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v___x_179_);
v___x_199_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__15));
v___x_200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_168_);
v___x_202_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16);
v___x_203_ = l_Std_Http_instReprHeaders_repr___redArg(v_headers_165_);
v___x_204_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set_uint8(v___x_205_, sizeof(void*)*1, v___x_174_);
v___x_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_201_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_177_);
v___x_208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___x_179_);
v___x_209_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__18));
v___x_210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_168_);
v___x_212_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19);
v___x_213_ = l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(v_bodyAction_166_, v___x_171_);
v___x_214_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*1, v___x_174_);
v___x_216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_211_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_177_);
v___x_218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v___x_179_);
v___x_219_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__21));
v___x_220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_168_);
v___x_222_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22);
v___x_223_ = l_Bool_repr___redArg(v_isCrossOrigin_167_);
v___x_224_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v___x_174_);
v___x_226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_221_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25);
v___x_228_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__26));
v___x_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___x_226_);
v___x_230_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__27));
v___x_231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_227_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*1, v___x_174_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr(lean_object* v_x_234_, lean_object* v_prec_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg(v_x_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___boxed(lean_object* v_x_237_, lean_object* v_prec_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_Http_Protocol_H1_instReprRedirectPlan_repr(v_x_237_, v_prec_238_);
lean_dec(v_prec_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___impl(lean_object* v_x_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_obj_tag_nat(v_x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___impl___boxed(lean_object* v_x_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___impl(v_x_244_);
lean_dec(v_x_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(lean_object* v_t_246_, lean_object* v_k_247_){
_start:
{
if (lean_obj_tag(v_t_246_) == 0)
{
return v_k_247_;
}
else
{
lean_object* v_plan_248_; lean_object* v___x_249_; 
v_plan_248_ = lean_ctor_get(v_t_246_, 0);
lean_inc_ref(v_plan_248_);
lean_dec_ref_known(v_t_246_, 1);
v___x_249_ = lean_apply_1(v_k_247_, v_plan_248_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim(lean_object* v_motive_250_, lean_object* v_ctorIdx_251_, lean_object* v_t_252_, lean_object* v_h_253_, lean_object* v_k_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_252_, v_k_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___boxed(lean_object* v_motive_256_, lean_object* v_ctorIdx_257_, lean_object* v_t_258_, lean_object* v_h_259_, lean_object* v_k_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim(v_motive_256_, v_ctorIdx_257_, v_t_258_, v_h_259_, v_k_260_);
lean_dec(v_ctorIdx_257_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_done_elim___redArg(lean_object* v_t_262_, lean_object* v_done_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_262_, v_done_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_done_elim(lean_object* v_motive_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_done_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_266_, v_done_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_follow_elim___redArg(lean_object* v_t_270_, lean_object* v_follow_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_270_, v_follow_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_follow_elim(lean_object* v_motive_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_follow_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_274_, v_follow_276_);
return v___x_277_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome_default(void){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_box(0);
return v___x_278_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome(void){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lean_box(0);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(lean_object* v_current_280_, lean_object* v_x_281_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v_uri_282_; lean_object* v_authority_283_; 
lean_dec_ref(v_current_280_);
v_uri_282_ = lean_ctor_get(v_x_281_, 0);
lean_inc_ref(v_uri_282_);
lean_dec_ref_known(v_x_281_, 1);
v_authority_283_ = lean_ctor_get(v_uri_282_, 1);
lean_inc(v_authority_283_);
if (lean_obj_tag(v_authority_283_) == 0)
{
lean_object* v___x_284_; 
lean_dec_ref(v_uri_282_);
v___x_284_ = lean_box(0);
return v___x_284_;
}
else
{
lean_object* v_val_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_303_; 
v_val_285_ = lean_ctor_get(v_authority_283_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v_authority_283_);
if (v_isSharedCheck_303_ == 0)
{
v___x_287_ = v_authority_283_;
v_isShared_288_ = v_isSharedCheck_303_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_val_285_);
lean_dec(v_authority_283_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_303_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v_scheme_289_; lean_object* v_host_290_; lean_object* v_port_291_; uint16_t v___y_293_; 
v_scheme_289_ = lean_ctor_get(v_uri_282_, 0);
lean_inc_ref(v_scheme_289_);
lean_dec_ref(v_uri_282_);
v_host_290_ = lean_ctor_get(v_val_285_, 1);
lean_inc(v_host_290_);
v_port_291_ = lean_ctor_get(v_val_285_, 2);
lean_inc(v_port_291_);
lean_dec(v_val_285_);
if (lean_obj_tag(v_port_291_) == 2)
{
uint16_t v_port_301_; 
v_port_301_ = lean_ctor_get_uint16(v_port_291_, 0);
lean_dec_ref_known(v_port_291_, 0);
v___y_293_ = v_port_301_;
goto v___jp_292_;
}
else
{
uint16_t v___x_302_; 
lean_dec(v_port_291_);
v___x_302_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_289_);
v___y_293_ = v___x_302_;
goto v___jp_292_;
}
v___jp_292_:
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_box(3);
v___x_295_ = l_Std_Http_URI_instBEqHost_beq(v_host_290_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_296_, 0, v_scheme_289_);
lean_ctor_set(v___x_296_, 1, v_host_290_);
lean_ctor_set_uint16(v___x_296_, sizeof(void*)*2, v___y_293_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_296_);
v___x_298_ = v___x_287_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
else
{
lean_object* v___x_300_; 
lean_dec(v_host_290_);
lean_dec_ref(v_scheme_289_);
lean_del_object(v___x_287_);
v___x_300_ = lean_box(0);
return v___x_300_;
}
}
}
}
}
else
{
lean_object* v_ref_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_336_; 
v_ref_304_ = lean_ctor_get(v_x_281_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_336_ == 0)
{
v___x_306_ = v_x_281_;
v_isShared_307_ = v_isSharedCheck_336_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_ref_304_);
lean_dec(v_x_281_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_336_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v_authority_308_; 
v_authority_308_ = lean_ctor_get(v_ref_304_, 0);
lean_inc(v_authority_308_);
lean_dec_ref(v_ref_304_);
if (lean_obj_tag(v_authority_308_) == 1)
{
lean_object* v_val_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_332_; 
lean_del_object(v___x_306_);
v_val_309_ = lean_ctor_get(v_authority_308_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v_authority_308_);
if (v_isSharedCheck_332_ == 0)
{
v___x_311_ = v_authority_308_;
v_isShared_312_ = v_isSharedCheck_332_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_val_309_);
lean_dec(v_authority_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_332_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v_host_313_; lean_object* v_port_314_; uint16_t v___y_316_; 
v_host_313_ = lean_ctor_get(v_val_309_, 1);
lean_inc(v_host_313_);
v_port_314_ = lean_ctor_get(v_val_309_, 2);
lean_inc(v_port_314_);
lean_dec(v_val_309_);
if (lean_obj_tag(v_port_314_) == 2)
{
uint16_t v_port_329_; 
v_port_329_ = lean_ctor_get_uint16(v_port_314_, 0);
lean_dec_ref_known(v_port_314_, 0);
v___y_316_ = v_port_329_;
goto v___jp_315_;
}
else
{
lean_object* v_scheme_330_; uint16_t v___x_331_; 
lean_dec(v_port_314_);
v_scheme_330_ = lean_ctor_get(v_current_280_, 0);
v___x_331_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_330_);
v___y_316_ = v___x_331_;
goto v___jp_315_;
}
v___jp_315_:
{
lean_object* v_scheme_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_327_; 
v_scheme_317_ = lean_ctor_get(v_current_280_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v_current_280_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v_current_280_, 1);
lean_dec(v_unused_328_);
v___x_319_ = v_current_280_;
v_isShared_320_ = v_isSharedCheck_327_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_scheme_317_);
lean_dec(v_current_280_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_327_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v_host_313_);
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_scheme_317_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_host_313_);
v___x_322_ = v_reuseFailAlloc_326_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_324_; 
lean_ctor_set_uint16(v___x_322_, sizeof(void*)*2, v___y_316_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_322_);
v___x_324_ = v___x_311_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
}
else
{
lean_object* v___x_334_; 
lean_dec(v_authority_308_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v_current_280_);
v___x_334_ = v___x_306_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_current_280_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(uint8_t v_originalMethod_337_, lean_object* v_x_338_){
_start:
{
switch(lean_obj_tag(v_x_338_))
{
case 17:
{
uint8_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = 9;
v___x_344_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_337_, v___x_343_);
if (v___x_344_ == 0)
{
uint8_t v___x_345_; 
v___x_345_ = 8;
return v___x_345_;
}
else
{
return v___x_343_;
}
}
case 15:
{
goto v___jp_339_;
}
case 16:
{
goto v___jp_339_;
}
default: 
{
return v_originalMethod_337_;
}
}
v___jp_339_:
{
uint8_t v___x_340_; uint8_t v___x_341_; 
v___x_340_ = 23;
v___x_341_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_337_, v___x_340_);
if (v___x_341_ == 0)
{
return v_originalMethod_337_;
}
else
{
uint8_t v___x_342_; 
v___x_342_ = 8;
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod___boxed(lean_object* v_originalMethod_346_, lean_object* v_x_347_){
_start:
{
uint8_t v_originalMethod_boxed_348_; uint8_t v_res_349_; lean_object* v_r_350_; 
v_originalMethod_boxed_348_ = lean_unbox(v_originalMethod_346_);
v_res_349_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_originalMethod_boxed_348_, v_x_347_);
lean_dec(v_x_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_351_ = l_Std_Http_Header_Name_transferEncoding;
v___x_352_ = l_Std_Http_Header_Name_keepAlive;
v___x_353_ = l_Std_Http_Header_Name_connection;
v___x_354_ = lean_unsigned_to_nat(3u);
v___x_355_ = lean_mk_empty_array_with_capacity(v___x_354_);
v___x_356_ = lean_array_push(v___x_355_, v___x_353_);
v___x_357_ = lean_array_push(v___x_356_, v___x_352_);
v___x_358_ = lean_array_push(v___x_357_, v___x_351_);
return v___x_358_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders(void){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(lean_object* v_as_360_, size_t v_i_361_, size_t v_stop_362_, lean_object* v_b_363_){
_start:
{
lean_object* v___y_365_; uint8_t v___x_369_; 
v___x_369_ = lean_usize_dec_eq(v_i_361_, v_stop_362_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_array_uget_borrowed(v_as_360_, v_i_361_);
lean_inc(v___x_370_);
v___x_371_ = l_Std_Http_Header_Name_ofString_x3f(v___x_370_);
if (lean_obj_tag(v___x_371_) == 0)
{
v___y_365_ = v_b_363_;
goto v___jp_364_;
}
else
{
lean_object* v_val_372_; lean_object* v___x_373_; 
v_val_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_val_372_);
lean_dec_ref_known(v___x_371_, 1);
v___x_373_ = lean_array_push(v_b_363_, v_val_372_);
v___y_365_ = v___x_373_;
goto v___jp_364_;
}
}
else
{
return v_b_363_;
}
v___jp_364_:
{
size_t v___x_366_; size_t v___x_367_; 
v___x_366_ = ((size_t)1ULL);
v___x_367_ = lean_usize_add(v_i_361_, v___x_366_);
v_i_361_ = v___x_367_;
v_b_363_ = v___y_365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0___boxed(lean_object* v_as_374_, lean_object* v_i_375_, lean_object* v_stop_376_, lean_object* v_b_377_){
_start:
{
size_t v_i_boxed_378_; size_t v_stop_boxed_379_; lean_object* v_res_380_; 
v_i_boxed_378_ = lean_unbox_usize(v_i_375_);
lean_dec(v_i_375_);
v_stop_boxed_379_ = lean_unbox_usize(v_stop_376_);
lean_dec(v_stop_376_);
v_res_380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_as_374_, v_i_boxed_378_, v_stop_boxed_379_, v_b_377_);
lean_dec_ref(v_as_374_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(lean_object* v_as_381_, size_t v_i_382_, size_t v_stop_383_, lean_object* v_b_384_){
_start:
{
lean_object* v___y_386_; uint8_t v___x_390_; 
v___x_390_ = lean_usize_dec_eq(v_i_382_, v_stop_383_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_array_uget_borrowed(v_as_381_, v_i_382_);
lean_inc(v___x_391_);
v___x_392_ = l_Std_Http_Header_Connection_parse(v___x_391_);
if (lean_obj_tag(v___x_392_) == 0)
{
v___y_386_ = v_b_384_;
goto v___jp_385_;
}
else
{
lean_object* v_val_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v_val_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_val_393_);
lean_dec_ref_known(v___x_392_, 1);
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = lean_array_get_size(v_val_393_);
v___x_396_ = lean_nat_dec_lt(v___x_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_dec(v_val_393_);
v___y_386_ = v_b_384_;
goto v___jp_385_;
}
else
{
size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; 
v___x_397_ = ((size_t)0ULL);
v___x_398_ = lean_usize_of_nat(v___x_395_);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_val_393_, v___x_397_, v___x_398_, v_b_384_);
lean_dec(v_val_393_);
v___y_386_ = v___x_399_;
goto v___jp_385_;
}
}
}
else
{
return v_b_384_;
}
v___jp_385_:
{
size_t v___x_387_; size_t v___x_388_; 
v___x_387_ = ((size_t)1ULL);
v___x_388_ = lean_usize_add(v_i_382_, v___x_387_);
v_i_382_ = v___x_388_;
v_b_384_ = v___y_386_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___boxed(lean_object* v_as_400_, lean_object* v_i_401_, lean_object* v_stop_402_, lean_object* v_b_403_){
_start:
{
size_t v_i_boxed_404_; size_t v_stop_boxed_405_; lean_object* v_res_406_; 
v_i_boxed_404_ = lean_unbox_usize(v_i_401_);
lean_dec(v_i_401_);
v_stop_boxed_405_ = lean_unbox_usize(v_stop_402_);
lean_dec(v_stop_402_);
v_res_406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(v_as_400_, v_i_boxed_404_, v_stop_boxed_405_, v_b_403_);
lean_dec_ref(v_as_400_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(lean_object* v_as_407_, size_t v_i_408_, size_t v_stop_409_, lean_object* v_b_410_){
_start:
{
lean_object* v___y_412_; uint8_t v___x_416_; 
v___x_416_ = lean_usize_dec_eq(v_i_408_, v_stop_409_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v_fst_418_; lean_object* v_snd_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_417_ = lean_array_uget_borrowed(v_as_407_, v_i_408_);
v_fst_418_ = lean_ctor_get(v___x_417_, 0);
v_snd_419_ = lean_ctor_get(v___x_417_, 1);
v___x_420_ = l_Std_Http_Header_Name_connection;
v___x_421_ = lean_string_dec_eq(v_fst_418_, v___x_420_);
if (v___x_421_ == 0)
{
v___y_412_ = v_b_410_;
goto v___jp_411_;
}
else
{
lean_object* v___x_422_; 
lean_inc(v_snd_419_);
v___x_422_ = lean_array_push(v_b_410_, v_snd_419_);
v___y_412_ = v___x_422_;
goto v___jp_411_;
}
}
else
{
return v_b_410_;
}
v___jp_411_:
{
size_t v___x_413_; size_t v___x_414_; 
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_add(v_i_408_, v___x_413_);
v_i_408_ = v___x_414_;
v_b_410_ = v___y_412_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___boxed(lean_object* v_as_423_, lean_object* v_i_424_, lean_object* v_stop_425_, lean_object* v_b_426_){
_start:
{
size_t v_i_boxed_427_; size_t v_stop_boxed_428_; lean_object* v_res_429_; 
v_i_boxed_427_ = lean_unbox_usize(v_i_424_);
lean_dec(v_i_424_);
v_stop_boxed_428_ = lean_unbox_usize(v_stop_425_);
lean_dec(v_stop_425_);
v_res_429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(v_as_423_, v_i_boxed_427_, v_stop_boxed_428_, v_b_426_);
lean_dec_ref(v_as_423_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(lean_object* v_headers_432_){
_start:
{
lean_object* v___y_434_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___x_446_ = lean_array_get_size(v_headers_432_);
v___x_447_ = lean_nat_dec_lt(v___x_444_, v___x_446_);
if (v___x_447_ == 0)
{
v___y_434_ = v___x_445_;
goto v___jp_433_;
}
else
{
size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v___x_448_ = ((size_t)0ULL);
v___x_449_ = lean_usize_of_nat(v___x_446_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(v_headers_432_, v___x_448_, v___x_449_, v___x_445_);
v___y_434_ = v___x_450_;
goto v___jp_433_;
}
v___jp_433_:
{
lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_435_ = lean_array_get_size(v___y_434_);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_nat_dec_eq(v___x_435_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___x_439_ = lean_nat_dec_lt(v___x_436_, v___x_435_);
if (v___x_439_ == 0)
{
lean_dec_ref(v___y_434_);
return v___x_438_;
}
else
{
size_t v___x_440_; size_t v___x_441_; lean_object* v___x_442_; 
v___x_440_ = ((size_t)0ULL);
v___x_441_ = lean_usize_of_nat(v___x_435_);
v___x_442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(v___y_434_, v___x_440_, v___x_441_, v___x_438_);
lean_dec_ref(v___y_434_);
return v___x_442_;
}
}
else
{
lean_object* v___x_443_; 
lean_dec_ref(v___y_434_);
v___x_443_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___boxed(lean_object* v_headers_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_451_);
lean_dec_ref(v_headers_451_);
return v_res_452_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_453_ = l_Std_Http_Header_Name_proxyAuthorization;
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_mk_empty_array_with_capacity(v___x_454_);
v___x_456_ = lean_array_push(v___x_455_, v___x_453_);
return v___x_456_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders(void){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0);
return v___x_457_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_458_ = l_Std_Http_Header_Name_referer;
v___x_459_ = l_Std_Http_Header_Name_cookie;
v___x_460_ = l_Std_Http_Header_Name_authorization;
v___x_461_ = lean_unsigned_to_nat(3u);
v___x_462_ = lean_mk_empty_array_with_capacity(v___x_461_);
v___x_463_ = lean_array_push(v___x_462_, v___x_460_);
v___x_464_ = lean_array_push(v___x_463_, v___x_459_);
v___x_465_ = lean_array_push(v___x_464_, v___x_458_);
return v___x_465_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders(void){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0);
return v___x_466_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_467_ = l_Std_Http_Header_Name_ifModifiedSince;
v___x_468_ = l_Std_Http_Header_Name_ifNoneMatch;
v___x_469_ = lean_unsigned_to_nat(2u);
v___x_470_ = lean_mk_empty_array_with_capacity(v___x_469_);
v___x_471_ = lean_array_push(v___x_470_, v___x_468_);
v___x_472_ = lean_array_push(v___x_471_, v___x_467_);
return v___x_472_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders(void){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0);
return v___x_473_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_474_ = l_Std_Http_Header_Name_lastModified;
v___x_475_ = l_Std_Http_Header_Name_contentLocation;
v___x_476_ = l_Std_Http_Header_Name_contentLanguage;
v___x_477_ = l_Std_Http_Header_Name_contentEncoding;
v___x_478_ = l_Std_Http_Header_Name_contentLength;
v___x_479_ = l_Std_Http_Header_Name_contentType;
v___x_480_ = lean_unsigned_to_nat(6u);
v___x_481_ = lean_mk_empty_array_with_capacity(v___x_480_);
v___x_482_ = lean_array_push(v___x_481_, v___x_479_);
v___x_483_ = lean_array_push(v___x_482_, v___x_478_);
v___x_484_ = lean_array_push(v___x_483_, v___x_477_);
v___x_485_ = lean_array_push(v___x_484_, v___x_476_);
v___x_486_ = lean_array_push(v___x_485_, v___x_475_);
v___x_487_ = lean_array_push(v___x_486_, v___x_474_);
return v___x_487_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders(void){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0);
return v___x_488_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(lean_object* v_a_489_, lean_object* v_as_490_, size_t v_i_491_, size_t v_stop_492_){
_start:
{
uint8_t v___x_493_; 
v___x_493_ = lean_usize_dec_eq(v_i_491_, v_stop_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = lean_array_uget_borrowed(v_as_490_, v_i_491_);
v___x_495_ = lean_string_dec_eq(v_a_489_, v___x_494_);
if (v___x_495_ == 0)
{
size_t v___x_496_; size_t v___x_497_; 
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_add(v_i_491_, v___x_496_);
v_i_491_ = v___x_497_;
goto _start;
}
else
{
return v___x_495_;
}
}
else
{
uint8_t v___x_499_; 
v___x_499_ = 0;
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___boxed(lean_object* v_a_500_, lean_object* v_as_501_, lean_object* v_i_502_, lean_object* v_stop_503_){
_start:
{
size_t v_i_boxed_504_; size_t v_stop_boxed_505_; uint8_t v_res_506_; lean_object* v_r_507_; 
v_i_boxed_504_ = lean_unbox_usize(v_i_502_);
lean_dec(v_i_502_);
v_stop_boxed_505_ = lean_unbox_usize(v_stop_503_);
lean_dec(v_stop_503_);
v_res_506_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_a_500_, v_as_501_, v_i_boxed_504_, v_stop_boxed_505_);
lean_dec_ref(v_as_501_);
lean_dec_ref(v_a_500_);
v_r_507_ = lean_box(v_res_506_);
return v_r_507_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(lean_object* v_as_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = lean_array_get_size(v_as_508_);
v___x_512_ = lean_nat_dec_lt(v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
return v___x_512_;
}
else
{
size_t v___x_513_; size_t v___x_514_; uint8_t v___x_515_; 
v___x_513_ = ((size_t)0ULL);
v___x_514_ = lean_usize_of_nat(v___x_511_);
v___x_515_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_a_509_, v_as_508_, v___x_513_, v___x_514_);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___boxed(lean_object* v_as_516_, lean_object* v_a_517_){
_start:
{
uint8_t v_res_518_; lean_object* v_r_519_; 
v_res_518_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v_as_516_, v_a_517_);
lean_dec_ref(v_a_517_);
lean_dec_ref(v_as_516_);
v_r_519_ = lean_box(v_res_518_);
return v_r_519_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(lean_object* v___y_520_, lean_object* v_as_521_, size_t v_i_522_, size_t v_stop_523_){
_start:
{
uint8_t v___x_524_; 
v___x_524_ = lean_usize_dec_eq(v_i_522_, v_stop_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v_fst_526_; uint8_t v___x_527_; 
v___x_525_ = lean_array_uget_borrowed(v_as_521_, v_i_522_);
v_fst_526_ = lean_ctor_get(v___x_525_, 0);
v___x_527_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v___y_520_, v_fst_526_);
if (v___x_527_ == 0)
{
size_t v___x_528_; size_t v___x_529_; 
v___x_528_ = ((size_t)1ULL);
v___x_529_ = lean_usize_add(v_i_522_, v___x_528_);
v_i_522_ = v___x_529_;
goto _start;
}
else
{
return v___x_527_;
}
}
else
{
uint8_t v___x_531_; 
v___x_531_ = 0;
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1___boxed(lean_object* v___y_532_, lean_object* v_as_533_, lean_object* v_i_534_, lean_object* v_stop_535_){
_start:
{
size_t v_i_boxed_536_; size_t v_stop_boxed_537_; uint8_t v_res_538_; lean_object* v_r_539_; 
v_i_boxed_536_ = lean_unbox_usize(v_i_534_);
lean_dec(v_i_534_);
v_stop_boxed_537_ = lean_unbox_usize(v_stop_535_);
lean_dec(v_stop_535_);
v_res_538_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(v___y_532_, v_as_533_, v_i_boxed_536_, v_stop_boxed_537_);
lean_dec_ref(v_as_533_);
lean_dec_ref(v___y_532_);
v_r_539_ = lean_box(v_res_538_);
return v_r_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_object* v___y_540_, lean_object* v_as_541_, size_t v_i_542_, size_t v_stop_543_, lean_object* v_b_544_){
_start:
{
lean_object* v___y_546_; uint8_t v___x_550_; 
v___x_550_ = lean_usize_dec_eq(v_i_542_, v_stop_543_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v_fst_552_; uint8_t v___x_553_; 
v___x_551_ = lean_array_uget_borrowed(v_as_541_, v_i_542_);
v_fst_552_ = lean_ctor_get(v___x_551_, 0);
v___x_553_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v___y_540_, v_fst_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
lean_inc(v___x_551_);
v___x_554_ = lean_array_push(v_b_544_, v___x_551_);
v___y_546_ = v___x_554_;
goto v___jp_545_;
}
else
{
v___y_546_ = v_b_544_;
goto v___jp_545_;
}
}
else
{
return v_b_544_;
}
v___jp_545_:
{
size_t v___x_547_; size_t v___x_548_; 
v___x_547_ = ((size_t)1ULL);
v___x_548_ = lean_usize_add(v_i_542_, v___x_547_);
v_i_542_ = v___x_548_;
v_b_544_ = v___y_546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___boxed(lean_object* v___y_555_, lean_object* v_as_556_, lean_object* v_i_557_, lean_object* v_stop_558_, lean_object* v_b_559_){
_start:
{
size_t v_i_boxed_560_; size_t v_stop_boxed_561_; lean_object* v_res_562_; 
v_i_boxed_560_ = lean_unbox_usize(v_i_557_);
lean_dec(v_i_557_);
v_stop_boxed_561_ = lean_unbox_usize(v_stop_558_);
lean_dec(v_stop_558_);
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(v___y_555_, v_as_556_, v_i_boxed_560_, v_stop_boxed_561_, v_b_559_);
lean_dec_ref(v_as_556_);
lean_dec_ref(v___y_555_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(lean_object* v_headers_565_, uint8_t v_isCrossOrigin_566_, uint8_t v_methodChanged_567_){
_start:
{
lean_object* v___y_569_; lean_object* v___y_579_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v_afterConnection_586_; 
v___x_584_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders;
v___x_585_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_565_);
v_afterConnection_586_ = l_Array_append___redArg(v___x_584_, v___x_585_);
lean_dec_ref(v___x_585_);
if (v_isCrossOrigin_566_ == 0)
{
v___y_579_ = v_afterConnection_586_;
goto v___jp_578_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_587_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders;
v___x_588_ = l_Array_append___redArg(v_afterConnection_586_, v___x_587_);
v___x_589_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders;
v___x_590_ = l_Array_append___redArg(v___x_588_, v___x_589_);
v___x_591_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_592_ = l_Array_append___redArg(v___x_590_, v___x_591_);
v___y_579_ = v___x_592_;
goto v___jp_578_;
}
v___jp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_array_get_size(v_headers_565_);
v___x_572_ = lean_nat_dec_lt(v___x_570_, v___x_571_);
if (v___x_572_ == 0)
{
lean_dec_ref(v___y_569_);
lean_inc_ref(v_headers_565_);
return v_headers_565_;
}
else
{
size_t v___x_573_; size_t v___x_574_; uint8_t v___x_575_; 
v___x_573_ = ((size_t)0ULL);
v___x_574_ = lean_usize_of_nat(v___x_571_);
v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(v___y_569_, v_headers_565_, v___x_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_dec_ref(v___y_569_);
lean_inc_ref(v_headers_565_);
return v_headers_565_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0));
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(v___y_569_, v_headers_565_, v___x_573_, v___x_574_, v___x_576_);
lean_dec_ref(v___y_569_);
return v___x_577_;
}
}
}
v___jp_578_:
{
if (v_methodChanged_567_ == 0)
{
v___y_569_ = v___y_579_;
goto v___jp_568_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_580_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders;
v___x_581_ = l_Array_append___redArg(v___y_579_, v___x_580_);
v___x_582_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_583_ = l_Array_append___redArg(v___x_581_, v___x_582_);
v___y_569_ = v___x_583_;
goto v___jp_568_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___boxed(lean_object* v_headers_593_, lean_object* v_isCrossOrigin_594_, lean_object* v_methodChanged_595_){
_start:
{
uint8_t v_isCrossOrigin_boxed_596_; uint8_t v_methodChanged_boxed_597_; lean_object* v_res_598_; 
v_isCrossOrigin_boxed_596_ = lean_unbox(v_isCrossOrigin_594_);
v_methodChanged_boxed_597_ = lean_unbox(v_methodChanged_595_);
v_res_598_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v_headers_593_, v_isCrossOrigin_boxed_596_, v_methodChanged_boxed_597_);
lean_dec_ref(v_headers_593_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg(lean_object* v_map_599_, lean_object* v_key_600_, lean_object* v_x_601_){
_start:
{
lean_object* v_zero_602_; uint8_t v_isZero_603_; 
v_zero_602_ = lean_unsigned_to_nat(0u);
v_isZero_603_ = lean_nat_dec_eq(v_x_601_, v_zero_602_);
if (v_isZero_603_ == 1)
{
lean_object* v___x_604_; 
lean_dec(v_x_601_);
v___x_604_ = lean_array_get_size(v_map_599_);
return v___x_604_;
}
else
{
lean_object* v_one_605_; lean_object* v_n_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_one_605_ = lean_unsigned_to_nat(1u);
v_n_606_ = lean_nat_sub(v_x_601_, v_one_605_);
lean_dec(v_x_601_);
v___x_607_ = lean_array_get_size(v_map_599_);
v___x_608_ = lean_nat_dec_lt(v_n_606_, v___x_607_);
if (v___x_608_ == 0)
{
lean_dec(v_n_606_);
return v___x_607_;
}
else
{
lean_object* v___x_609_; lean_object* v_fst_610_; uint8_t v___x_611_; 
v___x_609_ = lean_array_fget_borrowed(v_map_599_, v_n_606_);
v_fst_610_ = lean_ctor_get(v___x_609_, 0);
v___x_611_ = lean_string_dec_eq(v_fst_610_, v_key_600_);
if (v___x_611_ == 0)
{
v_x_601_ = v_n_606_;
goto _start;
}
else
{
return v_n_606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg___boxed(lean_object* v_map_613_, lean_object* v_key_614_, lean_object* v_x_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg(v_map_613_, v_key_614_, v_x_615_);
lean_dec_ref(v_key_614_);
lean_dec_ref(v_map_613_);
return v_res_616_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(lean_object* v_as_617_, size_t v_i_618_, size_t v_stop_619_){
_start:
{
uint8_t v___x_620_; 
v___x_620_ = lean_usize_dec_eq(v_i_618_, v_stop_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v_fst_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_621_ = lean_array_uget_borrowed(v_as_617_, v_i_618_);
v_fst_622_ = lean_ctor_get(v___x_621_, 0);
v___x_623_ = l_Std_Http_Header_Name_host;
v___x_624_ = lean_string_dec_eq(v_fst_622_, v___x_623_);
if (v___x_624_ == 0)
{
size_t v___x_625_; size_t v___x_626_; 
v___x_625_ = ((size_t)1ULL);
v___x_626_ = lean_usize_add(v_i_618_, v___x_625_);
v_i_618_ = v___x_626_;
goto _start;
}
else
{
return v___x_624_;
}
}
else
{
uint8_t v___x_628_; 
v___x_628_ = 0;
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___boxed(lean_object* v_as_629_, lean_object* v_i_630_, lean_object* v_stop_631_){
_start:
{
size_t v_i_boxed_632_; size_t v_stop_boxed_633_; uint8_t v_res_634_; lean_object* v_r_635_; 
v_i_boxed_632_ = lean_unbox_usize(v_i_630_);
lean_dec(v_i_630_);
v_stop_boxed_633_ = lean_unbox_usize(v_stop_631_);
lean_dec(v_stop_631_);
v_res_634_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(v_as_629_, v_i_boxed_632_, v_stop_boxed_633_);
lean_dec_ref(v_as_629_);
v_r_635_ = lean_box(v_res_634_);
return v_r_635_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(lean_object* v_headers_636_, lean_object* v_origin_637_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = lean_array_get_size(v_headers_636_);
v___x_640_ = lean_nat_dec_lt(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_dec_ref(v_origin_637_);
return v_headers_636_;
}
else
{
size_t v___x_641_; size_t v___x_642_; uint8_t v___x_643_; 
v___x_641_ = ((size_t)0ULL);
v___x_642_ = lean_usize_of_nat(v___x_639_);
v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(v_headers_636_, v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
lean_dec_ref(v_origin_637_);
return v_headers_636_;
}
else
{
lean_object* v___x_644_; lean_object* v_i_645_; uint8_t v___x_646_; 
v___x_644_ = l_Std_Http_Header_Name_host;
v_i_645_ = l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg(v_headers_636_, v___x_644_, v___x_639_);
v___x_646_ = lean_nat_dec_lt(v_i_645_, v___x_639_);
if (v___x_646_ == 0)
{
lean_dec(v_i_645_);
lean_dec_ref(v_origin_637_);
return v_headers_636_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_647_ = l_Std_Http_URI_Origin_hostHeader(v_origin_637_);
v___x_648_ = l_Std_Http_Header_Value_ofString_x21(v___x_647_);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_644_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = lean_array_fset(v_headers_636_, v_i_645_, v___x_649_);
lean_dec(v_i_645_);
return v___x_650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1(lean_object* v_00_u03b2_651_, lean_object* v_map_652_, lean_object* v_key_653_, lean_object* v_x_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg(v_map_652_, v_key_653_, v_x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___boxed(lean_object* v_00_u03b2_656_, lean_object* v_map_657_, lean_object* v_key_658_, lean_object* v_x_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1(v_00_u03b2_656_, v_map_657_, v_key_658_, v_x_659_);
lean_dec_ref(v_key_658_);
lean_dec_ref(v_map_657_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(lean_object* v_x_661_){
_start:
{
switch(lean_obj_tag(v_x_661_))
{
case 0:
{
lean_object* v_query_662_; 
v_query_662_ = lean_ctor_get(v_x_661_, 1);
lean_inc(v_query_662_);
return v_query_662_;
}
case 1:
{
lean_object* v_uri_663_; lean_object* v_query_664_; 
v_uri_663_ = lean_ctor_get(v_x_661_, 0);
v_query_664_ = lean_ctor_get(v_uri_663_, 3);
lean_inc(v_query_664_);
return v_query_664_;
}
default: 
{
lean_object* v___x_665_; 
v___x_665_ = lean_box(0);
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f___boxed(lean_object* v_x_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v_x_666_);
lean_dec(v_x_666_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolvedPath(lean_object* v_path_668_){
_start:
{
lean_object* v___x_669_; lean_object* v_segments_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_678_; 
v___x_669_ = l_Std_Http_URI_Path_normalize(v_path_668_);
v_segments_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_678_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_segments_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
uint8_t v___x_674_; lean_object* v___x_676_; 
v___x_674_ = 1;
if (v_isShared_673_ == 0)
{
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_segments_670_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*1, v___x_674_);
return v___x_676_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(lean_object* v_ref_679_, uint8_t v_isCrossOrigin_680_, lean_object* v_basePath_681_, lean_object* v_baseQuery_682_, lean_object* v_currentScheme_683_){
_start:
{
lean_object* v___y_685_; lean_object* v___y_686_; 
if (lean_obj_tag(v_ref_679_) == 0)
{
lean_object* v_uri_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref(v_currentScheme_683_);
lean_dec(v_baseQuery_682_);
lean_dec_ref(v_basePath_681_);
v_uri_689_ = lean_ctor_get(v_ref_679_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_ref_679_);
if (v_isSharedCheck_732_ == 0)
{
v___x_691_ = v_ref_679_;
v_isShared_692_ = v_isSharedCheck_732_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_uri_689_);
lean_dec(v_ref_679_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_732_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v_scheme_693_; lean_object* v_authority_694_; lean_object* v_path_695_; lean_object* v_query_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_730_; 
v_scheme_693_ = lean_ctor_get(v_uri_689_, 0);
v_authority_694_ = lean_ctor_get(v_uri_689_, 1);
v_path_695_ = lean_ctor_get(v_uri_689_, 2);
v_query_696_ = lean_ctor_get(v_uri_689_, 3);
v_isSharedCheck_730_ = !lean_is_exclusive(v_uri_689_);
if (v_isSharedCheck_730_ == 0)
{
lean_object* v_unused_731_; 
v_unused_731_ = lean_ctor_get(v_uri_689_, 4);
lean_dec(v_unused_731_);
v___x_698_ = v_uri_689_;
v_isShared_699_ = v_isSharedCheck_730_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_query_696_);
lean_inc(v_path_695_);
lean_inc(v_authority_694_);
lean_inc(v_scheme_693_);
lean_dec(v_uri_689_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_730_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___y_701_; 
if (lean_obj_tag(v_authority_694_) == 0)
{
v___y_701_ = v_authority_694_;
goto v___jp_700_;
}
else
{
lean_object* v_val_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_729_; 
v_val_711_ = lean_ctor_get(v_authority_694_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v_authority_694_);
if (v_isSharedCheck_729_ == 0)
{
v___x_713_ = v_authority_694_;
v_isShared_714_ = v_isSharedCheck_729_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_val_711_);
lean_dec(v_authority_694_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_729_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v_host_715_; lean_object* v_port_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_727_; 
v_host_715_ = lean_ctor_get(v_val_711_, 1);
v_port_716_ = lean_ctor_get(v_val_711_, 2);
v_isSharedCheck_727_ = !lean_is_exclusive(v_val_711_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; 
v_unused_728_ = lean_ctor_get(v_val_711_, 0);
lean_dec(v_unused_728_);
v___x_718_ = v_val_711_;
v_isShared_719_ = v_isSharedCheck_727_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_port_716_);
lean_inc(v_host_715_);
lean_dec(v_val_711_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_727_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_720_ = lean_box(0);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_720_);
v___x_722_ = v___x_718_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_host_715_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_port_716_);
v___x_722_ = v_reuseFailAlloc_726_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_724_; 
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_722_);
v___x_724_ = v___x_713_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
v___y_701_ = v___x_724_;
goto v___jp_700_;
}
}
}
}
}
v___jp_700_:
{
lean_object* v___x_702_; 
v___x_702_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolvedPath(v_path_695_);
if (v_isCrossOrigin_680_ == 0)
{
lean_object* v___x_703_; 
lean_dec(v___y_701_);
lean_del_object(v___x_698_);
lean_dec_ref(v_scheme_693_);
lean_del_object(v___x_691_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v_query_696_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; lean_object* v_stripped_706_; 
v___x_704_ = lean_box(0);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 4, v___x_704_);
lean_ctor_set(v___x_698_, 2, v___x_702_);
lean_ctor_set(v___x_698_, 1, v___y_701_);
v_stripped_706_ = v___x_698_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_scheme_693_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___y_701_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_query_696_);
lean_ctor_set(v_reuseFailAlloc_710_, 4, v___x_704_);
v_stripped_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set_tag(v___x_691_, 1);
lean_ctor_set(v___x_691_, 0, v_stripped_706_);
v___x_708_ = v___x_691_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_stripped_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
}
}
else
{
lean_object* v_ref_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_774_; 
v_ref_733_ = lean_ctor_get(v_ref_679_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v_ref_679_);
if (v_isSharedCheck_774_ == 0)
{
v___x_735_ = v_ref_679_;
v_isShared_736_ = v_isSharedCheck_774_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_ref_733_);
lean_dec(v_ref_679_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_774_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_authority_737_; lean_object* v_path_738_; lean_object* v_query_739_; lean_object* v___y_741_; 
v_authority_737_ = lean_ctor_get(v_ref_733_, 0);
lean_inc(v_authority_737_);
v_path_738_ = lean_ctor_get(v_ref_733_, 1);
lean_inc_ref(v_path_738_);
v_query_739_ = lean_ctor_get(v_ref_733_, 2);
lean_inc(v_query_739_);
lean_dec_ref(v_ref_733_);
if (lean_obj_tag(v_authority_737_) == 0)
{
uint8_t v_absolute_742_; uint8_t v___y_744_; 
lean_del_object(v___x_735_);
lean_dec_ref(v_currentScheme_683_);
v_absolute_742_ = lean_ctor_get_uint8(v_path_738_, sizeof(void*)*1);
if (v_absolute_742_ == 0)
{
uint8_t v___x_747_; 
v___x_747_ = l_Std_Http_URI_Path_isEmpty(v_path_738_);
v___y_744_ = v___x_747_;
goto v___jp_743_;
}
else
{
uint8_t v___x_748_; 
v___x_748_ = 0;
v___y_744_ = v___x_748_;
goto v___jp_743_;
}
v___jp_743_:
{
if (v_absolute_742_ == 0)
{
if (v___y_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec(v_baseQuery_682_);
v___x_745_ = l_Std_Http_URI_Path_parent(v_basePath_681_);
v___x_746_ = l_Std_Http_URI_Path_join(v___x_745_, v_path_738_);
lean_dec_ref(v_path_738_);
v___y_685_ = v___x_746_;
v___y_686_ = v_query_739_;
goto v___jp_684_;
}
else
{
lean_dec_ref(v_path_738_);
v___y_741_ = v_basePath_681_;
goto v___jp_740_;
}
}
else
{
lean_dec_ref(v_basePath_681_);
if (v___y_744_ == 0)
{
lean_dec(v_baseQuery_682_);
v___y_685_ = v_path_738_;
v___y_686_ = v_query_739_;
goto v___jp_684_;
}
else
{
v___y_741_ = v_path_738_;
goto v___jp_740_;
}
}
}
}
else
{
lean_object* v_val_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_baseQuery_682_);
lean_dec_ref(v_basePath_681_);
v_val_749_ = lean_ctor_get(v_authority_737_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v_authority_737_);
if (v_isSharedCheck_773_ == 0)
{
v___x_751_ = v_authority_737_;
v_isShared_752_ = v_isSharedCheck_773_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_val_749_);
lean_dec(v_authority_737_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_773_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_path_753_; 
v_path_753_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolvedPath(v_path_738_);
if (v_isCrossOrigin_680_ == 0)
{
lean_object* v___x_754_; 
lean_del_object(v___x_751_);
lean_dec(v_val_749_);
lean_del_object(v___x_735_);
lean_dec_ref(v_currentScheme_683_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_path_753_);
lean_ctor_set(v___x_754_, 1, v_query_739_);
return v___x_754_;
}
else
{
lean_object* v_host_755_; lean_object* v_port_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_771_; 
v_host_755_ = lean_ctor_get(v_val_749_, 1);
v_port_756_ = lean_ctor_get(v_val_749_, 2);
v_isSharedCheck_771_ = !lean_is_exclusive(v_val_749_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v_val_749_, 0);
lean_dec(v_unused_772_);
v___x_758_ = v_val_749_;
v_isShared_759_ = v_isSharedCheck_771_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_port_756_);
lean_inc(v_host_755_);
lean_dec(v_val_749_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_771_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v_stripped_762_; 
v___x_760_ = lean_box(0);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_760_);
v_stripped_762_ = v___x_758_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_host_755_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_port_756_);
v_stripped_762_ = v_reuseFailAlloc_770_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_764_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v_stripped_762_);
v___x_764_ = v___x_751_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_stripped_762_);
v___x_764_ = v_reuseFailAlloc_769_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v_af_765_; lean_object* v___x_767_; 
v_af_765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_af_765_, 0, v_currentScheme_683_);
lean_ctor_set(v_af_765_, 1, v___x_764_);
lean_ctor_set(v_af_765_, 2, v_path_753_);
lean_ctor_set(v_af_765_, 3, v_query_739_);
lean_ctor_set(v_af_765_, 4, v___x_760_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v_af_765_);
v___x_767_ = v___x_735_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_af_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
}
v___jp_740_:
{
if (lean_obj_tag(v_query_739_) == 0)
{
v___y_685_ = v___y_741_;
v___y_686_ = v_baseQuery_682_;
goto v___jp_684_;
}
else
{
lean_dec(v_baseQuery_682_);
v___y_685_ = v___y_741_;
v___y_686_ = v_query_739_;
goto v___jp_684_;
}
}
}
}
v___jp_684_:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolvedPath(v___y_685_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___y_686_);
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget___boxed(lean_object* v_ref_775_, lean_object* v_isCrossOrigin_776_, lean_object* v_basePath_777_, lean_object* v_baseQuery_778_, lean_object* v_currentScheme_779_){
_start:
{
uint8_t v_isCrossOrigin_boxed_780_; lean_object* v_res_781_; 
v_isCrossOrigin_boxed_780_ = lean_unbox(v_isCrossOrigin_776_);
v_res_781_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v_ref_775_, v_isCrossOrigin_boxed_780_, v_basePath_777_, v_baseQuery_778_, v_currentScheme_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0(lean_object* v___x_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Std_Http_URI_Parser_parseURIReference(v___x_785_, v___y_786_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_pos_788_; lean_object* v_array_789_; lean_object* v_idx_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v_pos_788_ = lean_ctor_get(v___x_787_, 0);
v_array_789_ = lean_ctor_get(v_pos_788_, 0);
v_idx_790_ = lean_ctor_get(v_pos_788_, 1);
v___x_791_ = lean_byte_array_size(v_array_789_);
v___x_792_ = lean_nat_dec_lt(v_idx_790_, v___x_791_);
if (v___x_792_ == 0)
{
return v___x_787_;
}
else
{
lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_800_; 
lean_inc(v_pos_788_);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; lean_object* v_unused_802_; 
v_unused_801_ = lean_ctor_get(v___x_787_, 1);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v___x_787_, 0);
lean_dec(v_unused_802_);
v___x_794_ = v___x_787_;
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
else
{
lean_dec(v___x_787_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1));
if (v_isShared_795_ == 0)
{
lean_ctor_set_tag(v___x_794_, 1);
lean_ctor_set(v___x_794_, 1, v___x_796_);
v___x_798_ = v___x_794_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_pos_788_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
else
{
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg(lean_object* v_map_803_, lean_object* v_key_804_, lean_object* v_i_805_){
_start:
{
lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_806_ = lean_array_get_size(v_map_803_);
v___x_807_ = lean_nat_dec_lt(v_i_805_, v___x_806_);
if (v___x_807_ == 0)
{
lean_dec(v_i_805_);
return v___x_806_;
}
else
{
lean_object* v___x_808_; lean_object* v_fst_809_; uint8_t v___x_810_; 
v___x_808_ = lean_array_fget_borrowed(v_map_803_, v_i_805_);
v_fst_809_ = lean_ctor_get(v___x_808_, 0);
v___x_810_ = lean_string_dec_eq(v_fst_809_, v_key_804_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_unsigned_to_nat(1u);
v___x_812_ = lean_nat_add(v_i_805_, v___x_811_);
lean_dec(v_i_805_);
v_i_805_ = v___x_812_;
goto _start;
}
else
{
return v_i_805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg___boxed(lean_object* v_map_814_, lean_object* v_key_815_, lean_object* v_i_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg(v_map_814_, v_key_815_, v_i_816_);
lean_dec_ref(v_key_815_);
lean_dec_ref(v_map_814_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect(lean_object* v_current_827_, lean_object* v_request_828_, uint8_t v_bodyReplayable_829_, lean_object* v_status_830_, lean_object* v_responseHeaders_831_){
_start:
{
uint16_t v___x_832_; uint16_t v___x_833_; uint8_t v___x_834_; 
v___x_832_ = 300;
v___x_833_ = l_Std_Http_Status_toCode(v_status_830_);
v___x_834_ = lean_uint16_dec_le(v___x_832_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
lean_dec_ref(v_current_827_);
v___x_835_ = lean_box(0);
return v___x_835_;
}
else
{
uint16_t v___x_836_; uint8_t v___x_837_; 
v___x_836_ = 400;
v___x_837_ = lean_uint16_dec_lt(v___x_833_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
lean_dec_ref(v_current_827_);
v___x_838_ = lean_box(0);
return v___x_838_;
}
else
{
uint8_t v_method_839_; lean_object* v_uri_840_; lean_object* v_headers_841_; uint8_t v___x_842_; uint8_t v___x_843_; 
v_method_839_ = lean_ctor_get_uint8(v_request_828_, sizeof(void*)*2);
v_uri_840_ = lean_ctor_get(v_request_828_, 0);
v_headers_841_ = lean_ctor_get(v_request_828_, 1);
v___x_842_ = 5;
v___x_843_ = l_Std_Http_instBEqMethod_beq(v_method_839_, v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_844_ = lean_box(19);
v___x_845_ = l_Std_Http_instBEqStatus_beq(v_status_830_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = lean_box(20);
v___x_847_ = l_Std_Http_instBEqStatus_beq(v_status_830_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_box(18);
v___x_849_ = l_Std_Http_instBEqStatus_beq(v_status_830_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_850_ = lean_box(14);
v___x_851_ = l_Std_Http_instBEqStatus_beq(v_status_830_, v___x_850_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v_i_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_852_ = l_Std_Http_Header_Name_location;
v___x_853_ = lean_unsigned_to_nat(0u);
v_i_854_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg(v_responseHeaders_831_, v___x_852_, v___x_853_);
v___x_855_ = lean_array_get_size(v_responseHeaders_831_);
v___x_856_ = lean_nat_dec_lt(v_i_854_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
lean_dec(v_i_854_);
lean_dec_ref(v_current_827_);
v___x_857_ = lean_box(0);
return v___x_857_;
}
else
{
lean_object* v___x_858_; lean_object* v_snd_859_; lean_object* v___f_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_858_ = lean_array_fget_borrowed(v_responseHeaders_831_, v_i_854_);
lean_dec(v_i_854_);
v_snd_859_ = lean_ctor_get(v___x_858_, 1);
v___f_860_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__1));
lean_inc(v_snd_859_);
v___x_861_ = lean_string_to_utf8(v_snd_859_);
v___x_862_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_860_, v___x_861_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v___x_863_; 
lean_dec_ref_known(v___x_862_, 1);
lean_dec_ref(v_current_827_);
v___x_863_ = lean_box(0);
return v___x_863_;
}
else
{
lean_object* v_a_864_; lean_object* v___x_865_; 
v_a_864_ = lean_ctor_get(v___x_862_, 0);
lean_inc_n(v_a_864_, 2);
lean_dec_ref_known(v___x_862_, 1);
lean_inc_ref(v_current_827_);
v___x_865_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(v_current_827_, v_a_864_);
if (lean_obj_tag(v___x_865_) == 1)
{
lean_object* v_val_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_941_; 
v_val_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_941_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_941_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_val_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_941_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_scheme_870_; uint8_t v_newMethod_871_; uint8_t v___y_873_; lean_object* v___y_874_; uint8_t v___y_875_; uint8_t v___y_885_; lean_object* v___y_886_; uint8_t v___y_889_; lean_object* v___y_890_; uint8_t v___y_891_; uint8_t v___y_898_; uint8_t v___y_899_; lean_object* v___y_900_; uint8_t v___y_901_; uint8_t v___y_905_; uint8_t v___y_906_; lean_object* v___y_907_; uint8_t v___y_908_; uint8_t v___y_912_; uint8_t v___y_913_; lean_object* v___y_914_; uint8_t v___y_915_; uint8_t v___y_919_; uint8_t v___y_920_; uint8_t v___y_921_; lean_object* v___y_922_; uint8_t v___y_924_; uint8_t v___y_925_; uint8_t v___y_926_; uint8_t v___y_930_; uint8_t v___y_931_; uint8_t v___y_934_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_scheme_870_ = lean_ctor_get(v_val_866_, 0);
v_newMethod_871_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_method_839_, v_status_830_);
v___x_936_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__2));
v___x_937_ = lean_string_dec_eq(v_scheme_870_, v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_938_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__3));
v___x_939_ = lean_string_dec_eq(v_scheme_870_, v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; 
lean_del_object(v___x_868_);
lean_dec(v_val_866_);
lean_dec(v_a_864_);
lean_dec_ref(v_current_827_);
v___x_940_ = lean_box(0);
return v___x_940_;
}
else
{
v___y_934_ = v___x_851_;
goto v___jp_933_;
}
}
else
{
v___y_934_ = v___x_851_;
goto v___jp_933_;
}
v___jp_872_:
{
lean_object* v_scheme_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v_rewrittenTarget_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v_scheme_876_ = lean_ctor_get(v_current_827_, 0);
lean_inc_ref(v_scheme_876_);
lean_dec_ref(v_current_827_);
v___x_877_ = l_Std_Http_RequestTarget_pathOrRoot(v_uri_840_);
v___x_878_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v_uri_840_);
v_rewrittenTarget_879_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v_a_864_, v___y_873_, v___x_877_, v___x_878_, v_scheme_876_);
v___x_880_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_880_, 0, v_val_866_);
lean_ctor_set(v___x_880_, 1, v_rewrittenTarget_879_);
lean_ctor_set(v___x_880_, 2, v___y_874_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*3, v_newMethod_871_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*3 + 1, v___y_875_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*3 + 2, v___y_873_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_880_);
v___x_882_ = v___x_868_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
v___jp_884_:
{
uint8_t v___x_887_; 
v___x_887_ = 0;
v___y_873_ = v___y_885_;
v___y_874_ = v___y_886_;
v___y_875_ = v___x_887_;
goto v___jp_872_;
}
v___jp_888_:
{
uint8_t v___x_892_; uint8_t v___x_893_; 
v___x_892_ = 8;
v___x_893_ = l_Std_Http_instBEqMethod_beq(v_newMethod_871_, v___x_892_);
if (v___x_893_ == 0)
{
uint8_t v___x_894_; uint8_t v___x_895_; 
v___x_894_ = 9;
v___x_895_ = l_Std_Http_instBEqMethod_beq(v_newMethod_871_, v___x_894_);
if (v___x_895_ == 0)
{
if (v___y_891_ == 0)
{
uint8_t v___x_896_; 
v___x_896_ = 1;
v___y_873_ = v___y_889_;
v___y_874_ = v___y_890_;
v___y_875_ = v___x_896_;
goto v___jp_872_;
}
else
{
v___y_885_ = v___y_889_;
v___y_886_ = v___y_890_;
goto v___jp_884_;
}
}
else
{
v___y_885_ = v___y_889_;
v___y_886_ = v___y_890_;
goto v___jp_884_;
}
}
else
{
v___y_885_ = v___y_889_;
v___y_886_ = v___y_890_;
goto v___jp_884_;
}
}
v___jp_897_:
{
if (v_bodyReplayable_829_ == 0)
{
lean_object* v___x_902_; 
lean_dec_ref(v___y_900_);
lean_del_object(v___x_868_);
lean_dec(v_val_866_);
lean_dec(v_a_864_);
lean_dec_ref(v_current_827_);
v___x_902_ = lean_box(0);
return v___x_902_;
}
else
{
if (v___y_899_ == 0)
{
v___y_889_ = v___y_898_;
v___y_890_ = v___y_900_;
v___y_891_ = v___y_901_;
goto v___jp_888_;
}
else
{
lean_object* v___x_903_; 
lean_dec_ref(v___y_900_);
lean_del_object(v___x_868_);
lean_dec(v_val_866_);
lean_dec(v_a_864_);
lean_dec_ref(v_current_827_);
v___x_903_ = lean_box(0);
return v___x_903_;
}
}
}
v___jp_904_:
{
uint8_t v___x_909_; uint8_t v___x_910_; 
v___x_909_ = 9;
v___x_910_ = l_Std_Http_instBEqMethod_beq(v_newMethod_871_, v___x_909_);
if (v___x_910_ == 0)
{
v___y_898_ = v___y_905_;
v___y_899_ = v___y_906_;
v___y_900_ = v___y_907_;
v___y_901_ = v___y_908_;
goto v___jp_897_;
}
else
{
if (v___y_906_ == 0)
{
v___y_889_ = v___y_905_;
v___y_890_ = v___y_907_;
v___y_891_ = v___y_908_;
goto v___jp_888_;
}
else
{
v___y_898_ = v___y_905_;
v___y_899_ = v___y_906_;
v___y_900_ = v___y_907_;
v___y_901_ = v___y_908_;
goto v___jp_897_;
}
}
}
v___jp_911_:
{
uint8_t v___x_916_; uint8_t v___x_917_; 
v___x_916_ = 8;
v___x_917_ = l_Std_Http_instBEqMethod_beq(v_newMethod_871_, v___x_916_);
if (v___x_917_ == 0)
{
v___y_905_ = v___y_912_;
v___y_906_ = v___y_913_;
v___y_907_ = v___y_914_;
v___y_908_ = v___y_915_;
goto v___jp_904_;
}
else
{
if (v___y_913_ == 0)
{
v___y_889_ = v___y_912_;
v___y_890_ = v___y_914_;
v___y_891_ = v___y_915_;
goto v___jp_888_;
}
else
{
v___y_905_ = v___y_912_;
v___y_906_ = v___y_913_;
v___y_907_ = v___y_914_;
v___y_908_ = v___y_915_;
goto v___jp_904_;
}
}
}
v___jp_918_:
{
if (v___y_921_ == 0)
{
v___y_912_ = v___y_919_;
v___y_913_ = v___y_920_;
v___y_914_ = v___y_922_;
v___y_915_ = v___y_921_;
goto v___jp_911_;
}
else
{
if (v___y_920_ == 0)
{
v___y_889_ = v___y_919_;
v___y_890_ = v___y_922_;
v___y_891_ = v___y_921_;
goto v___jp_888_;
}
else
{
v___y_912_ = v___y_919_;
v___y_913_ = v___y_920_;
v___y_914_ = v___y_922_;
v___y_915_ = v___y_921_;
goto v___jp_911_;
}
}
}
v___jp_923_:
{
lean_object* v_scrubbed_927_; 
v_scrubbed_927_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v_headers_841_, v___y_924_, v___y_926_);
if (v___y_924_ == 0)
{
v___y_919_ = v___y_924_;
v___y_920_ = v___y_925_;
v___y_921_ = v___y_926_;
v___y_922_ = v_scrubbed_927_;
goto v___jp_918_;
}
else
{
lean_object* v___x_928_; 
lean_inc(v_val_866_);
v___x_928_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(v_scrubbed_927_, v_val_866_);
v___y_919_ = v___y_924_;
v___y_920_ = v___y_925_;
v___y_921_ = v___y_926_;
v___y_922_ = v___x_928_;
goto v___jp_918_;
}
}
v___jp_929_:
{
uint8_t v___x_932_; 
v___x_932_ = l_Std_Http_instBEqMethod_beq(v_newMethod_871_, v_method_839_);
if (v___x_932_ == 0)
{
v___y_924_ = v___y_931_;
v___y_925_ = v___y_930_;
v___y_926_ = v___x_856_;
goto v___jp_923_;
}
else
{
v___y_924_ = v___y_931_;
v___y_925_ = v___y_930_;
v___y_926_ = v___y_930_;
goto v___jp_923_;
}
}
v___jp_933_:
{
uint8_t v___x_935_; 
v___x_935_ = l_Std_Http_URI_instBEqOrigin_beq(v_val_866_, v_current_827_);
if (v___x_935_ == 0)
{
v___y_930_ = v___y_934_;
v___y_931_ = v___x_856_;
goto v___jp_929_;
}
else
{
v___y_930_ = v___y_934_;
v___y_931_ = v___y_934_;
goto v___jp_929_;
}
}
}
}
else
{
lean_object* v___x_942_; 
lean_dec(v___x_865_);
lean_dec(v_a_864_);
lean_dec_ref(v_current_827_);
v___x_942_ = lean_box(0);
return v___x_942_;
}
}
}
}
else
{
lean_object* v___x_943_; 
lean_dec_ref(v_current_827_);
v___x_943_ = lean_box(0);
return v___x_943_;
}
}
else
{
lean_object* v___x_944_; 
lean_dec_ref(v_current_827_);
v___x_944_ = lean_box(0);
return v___x_944_;
}
}
else
{
lean_object* v___x_945_; 
lean_dec_ref(v_current_827_);
v___x_945_ = lean_box(0);
return v___x_945_;
}
}
else
{
lean_object* v___x_946_; 
lean_dec_ref(v_current_827_);
v___x_946_ = lean_box(0);
return v___x_946_;
}
}
else
{
lean_object* v___x_947_; 
lean_dec_ref(v_current_827_);
v___x_947_ = lean_box(0);
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___boxed(lean_object* v_current_948_, lean_object* v_request_949_, lean_object* v_bodyReplayable_950_, lean_object* v_status_951_, lean_object* v_responseHeaders_952_){
_start:
{
uint8_t v_bodyReplayable_boxed_953_; lean_object* v_res_954_; 
v_bodyReplayable_boxed_953_ = lean_unbox(v_bodyReplayable_950_);
v_res_954_ = l_Std_Http_Protocol_H1_decideRedirect(v_current_948_, v_request_949_, v_bodyReplayable_boxed_953_, v_status_951_, v_responseHeaders_952_);
lean_dec_ref(v_responseHeaders_952_);
lean_dec(v_status_951_);
lean_dec_ref(v_request_949_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0(lean_object* v_00_u03b2_955_, lean_object* v_map_956_, lean_object* v_key_957_, lean_object* v_i_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg(v_map_956_, v_key_957_, v_i_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___boxed(lean_object* v_00_u03b2_960_, lean_object* v_map_961_, lean_object* v_key_962_, lean_object* v_i_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0(v_00_u03b2_960_, v_map_961_, v_key_962_, v_i_963_);
lean_dec_ref(v_key_962_);
lean_dec_ref(v_map_961_);
return v_res_964_;
}
}
lean_object* runtime_initialize_Std_Http_Data_Request(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Status(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_URI(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Protocol_H1_Redirect(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Status(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_URI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction_default = _init_l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction_default();
l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction = _init_l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction();
l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome_default = _init_l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome_default();
lean_mark_persistent(l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome_default);
l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome = _init_l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome();
lean_mark_persistent(l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome);
l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders = _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders();
lean_mark_persistent(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders);
l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders = _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders();
lean_mark_persistent(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders);
l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders = _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders();
lean_mark_persistent(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders);
l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders = _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders();
lean_mark_persistent(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders);
l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders = _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders();
lean_mark_persistent(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Protocol_H1_Redirect(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Http_Data_Request(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Status(uint8_t builtin);
lean_object* initialize_Std_Http_Data_URI(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Protocol_H1_Redirect(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Http_Data_Request(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Status(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_URI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Redirect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Protocol_H1_Redirect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Protocol_H1_Redirect(builtin);
}
#ifdef __cplusplus
}
#endif
