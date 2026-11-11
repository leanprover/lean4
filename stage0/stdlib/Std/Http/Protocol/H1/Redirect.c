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
lean_object* v_val_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_300_; 
v_val_285_ = lean_ctor_get(v_authority_283_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v_authority_283_);
if (v_isSharedCheck_300_ == 0)
{
v___x_287_ = v_authority_283_;
v_isShared_288_ = v_isSharedCheck_300_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_val_285_);
lean_dec(v_authority_283_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_300_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v_scheme_289_; lean_object* v_host_290_; lean_object* v_port_291_; uint16_t v___y_293_; 
v_scheme_289_ = lean_ctor_get(v_uri_282_, 0);
lean_inc_ref(v_scheme_289_);
lean_dec_ref(v_uri_282_);
v_host_290_ = lean_ctor_get(v_val_285_, 1);
lean_inc_ref(v_host_290_);
v_port_291_ = lean_ctor_get(v_val_285_, 2);
lean_inc(v_port_291_);
lean_dec(v_val_285_);
if (lean_obj_tag(v_port_291_) == 2)
{
uint16_t v_port_298_; 
v_port_298_ = lean_ctor_get_uint16(v_port_291_, 0);
lean_dec_ref_known(v_port_291_, 0);
v___y_293_ = v_port_298_;
goto v___jp_292_;
}
else
{
uint16_t v___x_299_; 
lean_dec(v_port_291_);
v___x_299_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_289_);
v___y_293_ = v___x_299_;
goto v___jp_292_;
}
v___jp_292_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_294_, 0, v_scheme_289_);
lean_ctor_set(v___x_294_, 1, v_host_290_);
lean_ctor_set_uint16(v___x_294_, sizeof(void*)*2, v___y_293_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_294_);
v___x_296_ = v___x_287_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
else
{
lean_object* v_ref_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_333_; 
v_ref_301_ = lean_ctor_get(v_x_281_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_333_ == 0)
{
v___x_303_ = v_x_281_;
v_isShared_304_ = v_isSharedCheck_333_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_ref_301_);
lean_dec(v_x_281_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_333_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v_authority_305_; 
v_authority_305_ = lean_ctor_get(v_ref_301_, 0);
lean_inc(v_authority_305_);
lean_dec_ref(v_ref_301_);
if (lean_obj_tag(v_authority_305_) == 1)
{
lean_object* v_val_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_329_; 
lean_del_object(v___x_303_);
v_val_306_ = lean_ctor_get(v_authority_305_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_authority_305_);
if (v_isSharedCheck_329_ == 0)
{
v___x_308_ = v_authority_305_;
v_isShared_309_ = v_isSharedCheck_329_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_val_306_);
lean_dec(v_authority_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_329_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_host_310_; lean_object* v_port_311_; uint16_t v___y_313_; 
v_host_310_ = lean_ctor_get(v_val_306_, 1);
lean_inc_ref(v_host_310_);
v_port_311_ = lean_ctor_get(v_val_306_, 2);
lean_inc(v_port_311_);
lean_dec(v_val_306_);
if (lean_obj_tag(v_port_311_) == 2)
{
uint16_t v_port_326_; 
v_port_326_ = lean_ctor_get_uint16(v_port_311_, 0);
lean_dec_ref_known(v_port_311_, 0);
v___y_313_ = v_port_326_;
goto v___jp_312_;
}
else
{
lean_object* v_scheme_327_; uint16_t v___x_328_; 
lean_dec(v_port_311_);
v_scheme_327_ = lean_ctor_get(v_current_280_, 0);
v___x_328_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_327_);
v___y_313_ = v___x_328_;
goto v___jp_312_;
}
v___jp_312_:
{
lean_object* v_scheme_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_324_; 
v_scheme_314_ = lean_ctor_get(v_current_280_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v_current_280_);
if (v_isSharedCheck_324_ == 0)
{
lean_object* v_unused_325_; 
v_unused_325_ = lean_ctor_get(v_current_280_, 1);
lean_dec(v_unused_325_);
v___x_316_ = v_current_280_;
v_isShared_317_ = v_isSharedCheck_324_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_scheme_314_);
lean_dec(v_current_280_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_324_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 1, v_host_310_);
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_scheme_314_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_host_310_);
v___x_319_ = v_reuseFailAlloc_323_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_321_; 
lean_ctor_set_uint16(v___x_319_, sizeof(void*)*2, v___y_313_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_319_);
v___x_321_ = v___x_308_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
}
else
{
lean_object* v___x_331_; 
lean_dec(v_authority_305_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v_current_280_);
v___x_331_ = v___x_303_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_current_280_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(uint8_t v_originalMethod_334_, lean_object* v_x_335_){
_start:
{
switch(lean_obj_tag(v_x_335_))
{
case 17:
{
uint8_t v___x_340_; uint8_t v___x_341_; 
v___x_340_ = 9;
v___x_341_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_334_, v___x_340_);
if (v___x_341_ == 0)
{
uint8_t v___x_342_; 
v___x_342_ = 8;
return v___x_342_;
}
else
{
return v___x_340_;
}
}
case 15:
{
goto v___jp_336_;
}
case 16:
{
goto v___jp_336_;
}
default: 
{
return v_originalMethod_334_;
}
}
v___jp_336_:
{
uint8_t v___x_337_; uint8_t v___x_338_; 
v___x_337_ = 23;
v___x_338_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_334_, v___x_337_);
if (v___x_338_ == 0)
{
return v_originalMethod_334_;
}
else
{
uint8_t v___x_339_; 
v___x_339_ = 8;
return v___x_339_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod___boxed(lean_object* v_originalMethod_343_, lean_object* v_x_344_){
_start:
{
uint8_t v_originalMethod_boxed_345_; uint8_t v_res_346_; lean_object* v_r_347_; 
v_originalMethod_boxed_345_ = lean_unbox(v_originalMethod_343_);
v_res_346_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_originalMethod_boxed_345_, v_x_344_);
lean_dec(v_x_344_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_348_ = l_Std_Http_Header_Name_transferEncoding;
v___x_349_ = l_Std_Http_Header_Name_keepAlive;
v___x_350_ = l_Std_Http_Header_Name_connection;
v___x_351_ = lean_unsigned_to_nat(3u);
v___x_352_ = lean_mk_empty_array_with_capacity(v___x_351_);
v___x_353_ = lean_array_push(v___x_352_, v___x_350_);
v___x_354_ = lean_array_push(v___x_353_, v___x_349_);
v___x_355_ = lean_array_push(v___x_354_, v___x_348_);
return v___x_355_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders(void){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(lean_object* v_as_357_, size_t v_i_358_, size_t v_stop_359_, lean_object* v_b_360_){
_start:
{
lean_object* v___y_362_; uint8_t v___x_366_; 
v___x_366_ = lean_usize_dec_eq(v_i_358_, v_stop_359_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_array_uget_borrowed(v_as_357_, v_i_358_);
lean_inc(v___x_367_);
v___x_368_ = l_Std_Http_Header_Name_ofString_x3f(v___x_367_);
if (lean_obj_tag(v___x_368_) == 0)
{
v___y_362_ = v_b_360_;
goto v___jp_361_;
}
else
{
lean_object* v_val_369_; lean_object* v___x_370_; 
v_val_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_val_369_);
lean_dec_ref_known(v___x_368_, 1);
v___x_370_ = lean_array_push(v_b_360_, v_val_369_);
v___y_362_ = v___x_370_;
goto v___jp_361_;
}
}
else
{
return v_b_360_;
}
v___jp_361_:
{
size_t v___x_363_; size_t v___x_364_; 
v___x_363_ = ((size_t)1ULL);
v___x_364_ = lean_usize_add(v_i_358_, v___x_363_);
v_i_358_ = v___x_364_;
v_b_360_ = v___y_362_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0___boxed(lean_object* v_as_371_, lean_object* v_i_372_, lean_object* v_stop_373_, lean_object* v_b_374_){
_start:
{
size_t v_i_boxed_375_; size_t v_stop_boxed_376_; lean_object* v_res_377_; 
v_i_boxed_375_ = lean_unbox_usize(v_i_372_);
lean_dec(v_i_372_);
v_stop_boxed_376_ = lean_unbox_usize(v_stop_373_);
lean_dec(v_stop_373_);
v_res_377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_as_371_, v_i_boxed_375_, v_stop_boxed_376_, v_b_374_);
lean_dec_ref(v_as_371_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(lean_object* v_as_378_, size_t v_i_379_, size_t v_stop_380_, lean_object* v_b_381_){
_start:
{
lean_object* v___y_383_; uint8_t v___x_387_; 
v___x_387_ = lean_usize_dec_eq(v_i_379_, v_stop_380_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_array_uget_borrowed(v_as_378_, v_i_379_);
lean_inc(v___x_388_);
v___x_389_ = l_Std_Http_Header_Connection_parse(v___x_388_);
if (lean_obj_tag(v___x_389_) == 0)
{
v___y_383_ = v_b_381_;
goto v___jp_382_;
}
else
{
lean_object* v_val_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v_val_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_val_390_);
lean_dec_ref_known(v___x_389_, 1);
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = lean_array_get_size(v_val_390_);
v___x_393_ = lean_nat_dec_lt(v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
lean_dec(v_val_390_);
v___y_383_ = v_b_381_;
goto v___jp_382_;
}
else
{
size_t v___x_394_; size_t v___x_395_; lean_object* v___x_396_; 
v___x_394_ = ((size_t)0ULL);
v___x_395_ = lean_usize_of_nat(v___x_392_);
v___x_396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_val_390_, v___x_394_, v___x_395_, v_b_381_);
lean_dec(v_val_390_);
v___y_383_ = v___x_396_;
goto v___jp_382_;
}
}
}
else
{
return v_b_381_;
}
v___jp_382_:
{
size_t v___x_384_; size_t v___x_385_; 
v___x_384_ = ((size_t)1ULL);
v___x_385_ = lean_usize_add(v_i_379_, v___x_384_);
v_i_379_ = v___x_385_;
v_b_381_ = v___y_383_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___boxed(lean_object* v_as_397_, lean_object* v_i_398_, lean_object* v_stop_399_, lean_object* v_b_400_){
_start:
{
size_t v_i_boxed_401_; size_t v_stop_boxed_402_; lean_object* v_res_403_; 
v_i_boxed_401_ = lean_unbox_usize(v_i_398_);
lean_dec(v_i_398_);
v_stop_boxed_402_ = lean_unbox_usize(v_stop_399_);
lean_dec(v_stop_399_);
v_res_403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(v_as_397_, v_i_boxed_401_, v_stop_boxed_402_, v_b_400_);
lean_dec_ref(v_as_397_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(lean_object* v_as_404_, size_t v_i_405_, size_t v_stop_406_, lean_object* v_b_407_){
_start:
{
lean_object* v___y_409_; uint8_t v___x_413_; 
v___x_413_ = lean_usize_dec_eq(v_i_405_, v_stop_406_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v_fst_415_; lean_object* v_snd_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_414_ = lean_array_uget_borrowed(v_as_404_, v_i_405_);
v_fst_415_ = lean_ctor_get(v___x_414_, 0);
v_snd_416_ = lean_ctor_get(v___x_414_, 1);
v___x_417_ = l_Std_Http_Header_Name_connection;
v___x_418_ = lean_string_dec_eq(v_fst_415_, v___x_417_);
if (v___x_418_ == 0)
{
v___y_409_ = v_b_407_;
goto v___jp_408_;
}
else
{
lean_object* v___x_419_; 
lean_inc(v_snd_416_);
v___x_419_ = lean_array_push(v_b_407_, v_snd_416_);
v___y_409_ = v___x_419_;
goto v___jp_408_;
}
}
else
{
return v_b_407_;
}
v___jp_408_:
{
size_t v___x_410_; size_t v___x_411_; 
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_add(v_i_405_, v___x_410_);
v_i_405_ = v___x_411_;
v_b_407_ = v___y_409_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___boxed(lean_object* v_as_420_, lean_object* v_i_421_, lean_object* v_stop_422_, lean_object* v_b_423_){
_start:
{
size_t v_i_boxed_424_; size_t v_stop_boxed_425_; lean_object* v_res_426_; 
v_i_boxed_424_ = lean_unbox_usize(v_i_421_);
lean_dec(v_i_421_);
v_stop_boxed_425_ = lean_unbox_usize(v_stop_422_);
lean_dec(v_stop_422_);
v_res_426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(v_as_420_, v_i_boxed_424_, v_stop_boxed_425_, v_b_423_);
lean_dec_ref(v_as_420_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(lean_object* v_headers_429_){
_start:
{
lean_object* v___y_431_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___x_443_ = lean_array_get_size(v_headers_429_);
v___x_444_ = lean_nat_dec_lt(v___x_441_, v___x_443_);
if (v___x_444_ == 0)
{
v___y_431_ = v___x_442_;
goto v___jp_430_;
}
else
{
size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v___x_445_ = ((size_t)0ULL);
v___x_446_ = lean_usize_of_nat(v___x_443_);
v___x_447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(v_headers_429_, v___x_445_, v___x_446_, v___x_442_);
v___y_431_ = v___x_447_;
goto v___jp_430_;
}
v___jp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_432_ = lean_array_get_size(v___y_431_);
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_nat_dec_eq(v___x_432_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___x_436_ = lean_nat_dec_lt(v___x_433_, v___x_432_);
if (v___x_436_ == 0)
{
lean_dec_ref(v___y_431_);
return v___x_435_;
}
else
{
size_t v___x_437_; size_t v___x_438_; lean_object* v___x_439_; 
v___x_437_ = ((size_t)0ULL);
v___x_438_ = lean_usize_of_nat(v___x_432_);
v___x_439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(v___y_431_, v___x_437_, v___x_438_, v___x_435_);
lean_dec_ref(v___y_431_);
return v___x_439_;
}
}
else
{
lean_object* v___x_440_; 
lean_dec_ref(v___y_431_);
v___x_440_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
return v___x_440_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___boxed(lean_object* v_headers_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_448_);
lean_dec_ref(v_headers_448_);
return v_res_449_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_450_ = l_Std_Http_Header_Name_proxyAuthorization;
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_mk_empty_array_with_capacity(v___x_451_);
v___x_453_ = lean_array_push(v___x_452_, v___x_450_);
return v___x_453_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders(void){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0);
return v___x_454_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_455_ = l_Std_Http_Header_Name_referer;
v___x_456_ = l_Std_Http_Header_Name_cookie;
v___x_457_ = l_Std_Http_Header_Name_authorization;
v___x_458_ = lean_unsigned_to_nat(3u);
v___x_459_ = lean_mk_empty_array_with_capacity(v___x_458_);
v___x_460_ = lean_array_push(v___x_459_, v___x_457_);
v___x_461_ = lean_array_push(v___x_460_, v___x_456_);
v___x_462_ = lean_array_push(v___x_461_, v___x_455_);
return v___x_462_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders(void){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0);
return v___x_463_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_464_ = l_Std_Http_Header_Name_ifModifiedSince;
v___x_465_ = l_Std_Http_Header_Name_ifNoneMatch;
v___x_466_ = lean_unsigned_to_nat(2u);
v___x_467_ = lean_mk_empty_array_with_capacity(v___x_466_);
v___x_468_ = lean_array_push(v___x_467_, v___x_465_);
v___x_469_ = lean_array_push(v___x_468_, v___x_464_);
return v___x_469_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders(void){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0);
return v___x_470_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_471_ = l_Std_Http_Header_Name_lastModified;
v___x_472_ = l_Std_Http_Header_Name_contentLocation;
v___x_473_ = l_Std_Http_Header_Name_contentLanguage;
v___x_474_ = l_Std_Http_Header_Name_contentEncoding;
v___x_475_ = l_Std_Http_Header_Name_contentLength;
v___x_476_ = l_Std_Http_Header_Name_contentType;
v___x_477_ = lean_unsigned_to_nat(6u);
v___x_478_ = lean_mk_empty_array_with_capacity(v___x_477_);
v___x_479_ = lean_array_push(v___x_478_, v___x_476_);
v___x_480_ = lean_array_push(v___x_479_, v___x_475_);
v___x_481_ = lean_array_push(v___x_480_, v___x_474_);
v___x_482_ = lean_array_push(v___x_481_, v___x_473_);
v___x_483_ = lean_array_push(v___x_482_, v___x_472_);
v___x_484_ = lean_array_push(v___x_483_, v___x_471_);
return v___x_484_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders(void){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0);
return v___x_485_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(lean_object* v_a_486_, lean_object* v_as_487_, size_t v_i_488_, size_t v_stop_489_){
_start:
{
uint8_t v___x_490_; 
v___x_490_ = lean_usize_dec_eq(v_i_488_, v_stop_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = lean_array_uget_borrowed(v_as_487_, v_i_488_);
v___x_492_ = lean_string_dec_eq(v_a_486_, v___x_491_);
if (v___x_492_ == 0)
{
size_t v___x_493_; size_t v___x_494_; 
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_add(v_i_488_, v___x_493_);
v_i_488_ = v___x_494_;
goto _start;
}
else
{
return v___x_492_;
}
}
else
{
uint8_t v___x_496_; 
v___x_496_ = 0;
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___boxed(lean_object* v_a_497_, lean_object* v_as_498_, lean_object* v_i_499_, lean_object* v_stop_500_){
_start:
{
size_t v_i_boxed_501_; size_t v_stop_boxed_502_; uint8_t v_res_503_; lean_object* v_r_504_; 
v_i_boxed_501_ = lean_unbox_usize(v_i_499_);
lean_dec(v_i_499_);
v_stop_boxed_502_ = lean_unbox_usize(v_stop_500_);
lean_dec(v_stop_500_);
v_res_503_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_a_497_, v_as_498_, v_i_boxed_501_, v_stop_boxed_502_);
lean_dec_ref(v_as_498_);
lean_dec_ref(v_a_497_);
v_r_504_ = lean_box(v_res_503_);
return v_r_504_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(lean_object* v_as_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_array_get_size(v_as_505_);
v___x_509_ = lean_nat_dec_lt(v___x_507_, v___x_508_);
if (v___x_509_ == 0)
{
return v___x_509_;
}
else
{
size_t v___x_510_; size_t v___x_511_; uint8_t v___x_512_; 
v___x_510_ = ((size_t)0ULL);
v___x_511_ = lean_usize_of_nat(v___x_508_);
v___x_512_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_a_506_, v_as_505_, v___x_510_, v___x_511_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___boxed(lean_object* v_as_513_, lean_object* v_a_514_){
_start:
{
uint8_t v_res_515_; lean_object* v_r_516_; 
v_res_515_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v_as_513_, v_a_514_);
lean_dec_ref(v_a_514_);
lean_dec_ref(v_as_513_);
v_r_516_ = lean_box(v_res_515_);
return v_r_516_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(lean_object* v___y_517_, lean_object* v_as_518_, size_t v_i_519_, size_t v_stop_520_){
_start:
{
uint8_t v___x_521_; 
v___x_521_ = lean_usize_dec_eq(v_i_519_, v_stop_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v_fst_523_; uint8_t v___x_524_; 
v___x_522_ = lean_array_uget_borrowed(v_as_518_, v_i_519_);
v_fst_523_ = lean_ctor_get(v___x_522_, 0);
v___x_524_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v___y_517_, v_fst_523_);
if (v___x_524_ == 0)
{
size_t v___x_525_; size_t v___x_526_; 
v___x_525_ = ((size_t)1ULL);
v___x_526_ = lean_usize_add(v_i_519_, v___x_525_);
v_i_519_ = v___x_526_;
goto _start;
}
else
{
return v___x_524_;
}
}
else
{
uint8_t v___x_528_; 
v___x_528_ = 0;
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1___boxed(lean_object* v___y_529_, lean_object* v_as_530_, lean_object* v_i_531_, lean_object* v_stop_532_){
_start:
{
size_t v_i_boxed_533_; size_t v_stop_boxed_534_; uint8_t v_res_535_; lean_object* v_r_536_; 
v_i_boxed_533_ = lean_unbox_usize(v_i_531_);
lean_dec(v_i_531_);
v_stop_boxed_534_ = lean_unbox_usize(v_stop_532_);
lean_dec(v_stop_532_);
v_res_535_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(v___y_529_, v_as_530_, v_i_boxed_533_, v_stop_boxed_534_);
lean_dec_ref(v_as_530_);
lean_dec_ref(v___y_529_);
v_r_536_ = lean_box(v_res_535_);
return v_r_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_object* v___y_537_, lean_object* v_as_538_, size_t v_i_539_, size_t v_stop_540_, lean_object* v_b_541_){
_start:
{
lean_object* v___y_543_; uint8_t v___x_547_; 
v___x_547_ = lean_usize_dec_eq(v_i_539_, v_stop_540_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v_fst_549_; uint8_t v___x_550_; 
v___x_548_ = lean_array_uget_borrowed(v_as_538_, v_i_539_);
v_fst_549_ = lean_ctor_get(v___x_548_, 0);
v___x_550_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v___y_537_, v_fst_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
lean_inc(v___x_548_);
v___x_551_ = lean_array_push(v_b_541_, v___x_548_);
v___y_543_ = v___x_551_;
goto v___jp_542_;
}
else
{
v___y_543_ = v_b_541_;
goto v___jp_542_;
}
}
else
{
return v_b_541_;
}
v___jp_542_:
{
size_t v___x_544_; size_t v___x_545_; 
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_add(v_i_539_, v___x_544_);
v_i_539_ = v___x_545_;
v_b_541_ = v___y_543_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___boxed(lean_object* v___y_552_, lean_object* v_as_553_, lean_object* v_i_554_, lean_object* v_stop_555_, lean_object* v_b_556_){
_start:
{
size_t v_i_boxed_557_; size_t v_stop_boxed_558_; lean_object* v_res_559_; 
v_i_boxed_557_ = lean_unbox_usize(v_i_554_);
lean_dec(v_i_554_);
v_stop_boxed_558_ = lean_unbox_usize(v_stop_555_);
lean_dec(v_stop_555_);
v_res_559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(v___y_552_, v_as_553_, v_i_boxed_557_, v_stop_boxed_558_, v_b_556_);
lean_dec_ref(v_as_553_);
lean_dec_ref(v___y_552_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(lean_object* v_headers_562_, uint8_t v_isCrossOrigin_563_, uint8_t v_methodChanged_564_){
_start:
{
lean_object* v___y_566_; lean_object* v___y_576_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v_afterConnection_583_; 
v___x_581_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders;
v___x_582_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_562_);
v_afterConnection_583_ = l_Array_append___redArg(v___x_581_, v___x_582_);
lean_dec_ref(v___x_582_);
if (v_isCrossOrigin_563_ == 0)
{
v___y_576_ = v_afterConnection_583_;
goto v___jp_575_;
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_584_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders;
v___x_585_ = l_Array_append___redArg(v_afterConnection_583_, v___x_584_);
v___x_586_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders;
v___x_587_ = l_Array_append___redArg(v___x_585_, v___x_586_);
v___x_588_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_589_ = l_Array_append___redArg(v___x_587_, v___x_588_);
v___y_576_ = v___x_589_;
goto v___jp_575_;
}
v___jp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_array_get_size(v_headers_562_);
v___x_569_ = lean_nat_dec_lt(v___x_567_, v___x_568_);
if (v___x_569_ == 0)
{
lean_dec_ref(v___y_566_);
lean_inc_ref(v_headers_562_);
return v_headers_562_;
}
else
{
size_t v___x_570_; size_t v___x_571_; uint8_t v___x_572_; 
v___x_570_ = ((size_t)0ULL);
v___x_571_ = lean_usize_of_nat(v___x_568_);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(v___y_566_, v_headers_562_, v___x_570_, v___x_571_);
if (v___x_572_ == 0)
{
lean_dec_ref(v___y_566_);
lean_inc_ref(v_headers_562_);
return v_headers_562_;
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0));
v___x_574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(v___y_566_, v_headers_562_, v___x_570_, v___x_571_, v___x_573_);
lean_dec_ref(v___y_566_);
return v___x_574_;
}
}
}
v___jp_575_:
{
if (v_methodChanged_564_ == 0)
{
v___y_566_ = v___y_576_;
goto v___jp_565_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_577_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders;
v___x_578_ = l_Array_append___redArg(v___y_576_, v___x_577_);
v___x_579_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_580_ = l_Array_append___redArg(v___x_578_, v___x_579_);
v___y_566_ = v___x_580_;
goto v___jp_565_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___boxed(lean_object* v_headers_590_, lean_object* v_isCrossOrigin_591_, lean_object* v_methodChanged_592_){
_start:
{
uint8_t v_isCrossOrigin_boxed_593_; uint8_t v_methodChanged_boxed_594_; lean_object* v_res_595_; 
v_isCrossOrigin_boxed_593_ = lean_unbox(v_isCrossOrigin_591_);
v_methodChanged_boxed_594_ = lean_unbox(v_methodChanged_592_);
v_res_595_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v_headers_590_, v_isCrossOrigin_boxed_593_, v_methodChanged_boxed_594_);
lean_dec_ref(v_headers_590_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg(lean_object* v_map_596_, lean_object* v_key_597_, lean_object* v_x_598_){
_start:
{
lean_object* v_zero_599_; uint8_t v_isZero_600_; 
v_zero_599_ = lean_unsigned_to_nat(0u);
v_isZero_600_ = lean_nat_dec_eq(v_x_598_, v_zero_599_);
if (v_isZero_600_ == 1)
{
lean_object* v___x_601_; 
lean_dec(v_x_598_);
v___x_601_ = lean_array_get_size(v_map_596_);
return v___x_601_;
}
else
{
lean_object* v_one_602_; lean_object* v_n_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v_one_602_ = lean_unsigned_to_nat(1u);
v_n_603_ = lean_nat_sub(v_x_598_, v_one_602_);
lean_dec(v_x_598_);
v___x_604_ = lean_array_get_size(v_map_596_);
v___x_605_ = lean_nat_dec_lt(v_n_603_, v___x_604_);
if (v___x_605_ == 0)
{
lean_dec(v_n_603_);
return v___x_604_;
}
else
{
lean_object* v___x_606_; lean_object* v_fst_607_; uint8_t v___x_608_; 
v___x_606_ = lean_array_fget_borrowed(v_map_596_, v_n_603_);
v_fst_607_ = lean_ctor_get(v___x_606_, 0);
v___x_608_ = lean_string_dec_eq(v_fst_607_, v_key_597_);
if (v___x_608_ == 0)
{
v_x_598_ = v_n_603_;
goto _start;
}
else
{
return v_n_603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg___boxed(lean_object* v_map_610_, lean_object* v_key_611_, lean_object* v_x_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg(v_map_610_, v_key_611_, v_x_612_);
lean_dec_ref(v_key_611_);
lean_dec_ref(v_map_610_);
return v_res_613_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(lean_object* v_as_614_, size_t v_i_615_, size_t v_stop_616_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = lean_usize_dec_eq(v_i_615_, v_stop_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v_fst_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_618_ = lean_array_uget_borrowed(v_as_614_, v_i_615_);
v_fst_619_ = lean_ctor_get(v___x_618_, 0);
v___x_620_ = l_Std_Http_Header_Name_host;
v___x_621_ = lean_string_dec_eq(v_fst_619_, v___x_620_);
if (v___x_621_ == 0)
{
size_t v___x_622_; size_t v___x_623_; 
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_i_615_, v___x_622_);
v_i_615_ = v___x_623_;
goto _start;
}
else
{
return v___x_621_;
}
}
else
{
uint8_t v___x_625_; 
v___x_625_ = 0;
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___boxed(lean_object* v_as_626_, lean_object* v_i_627_, lean_object* v_stop_628_){
_start:
{
size_t v_i_boxed_629_; size_t v_stop_boxed_630_; uint8_t v_res_631_; lean_object* v_r_632_; 
v_i_boxed_629_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_stop_boxed_630_ = lean_unbox_usize(v_stop_628_);
lean_dec(v_stop_628_);
v_res_631_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(v_as_626_, v_i_boxed_629_, v_stop_boxed_630_);
lean_dec_ref(v_as_626_);
v_r_632_ = lean_box(v_res_631_);
return v_r_632_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(lean_object* v_headers_633_, lean_object* v_origin_634_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_array_get_size(v_headers_633_);
v___x_637_ = lean_nat_dec_lt(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_dec_ref(v_origin_634_);
return v_headers_633_;
}
else
{
size_t v___x_638_; size_t v___x_639_; uint8_t v___x_640_; 
v___x_638_ = ((size_t)0ULL);
v___x_639_ = lean_usize_of_nat(v___x_636_);
v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(v_headers_633_, v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_dec_ref(v_origin_634_);
return v_headers_633_;
}
else
{
lean_object* v___x_641_; lean_object* v_i_642_; uint8_t v___x_643_; 
v___x_641_ = l_Std_Http_Header_Name_host;
v_i_642_ = l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg(v_headers_633_, v___x_641_, v___x_636_);
v___x_643_ = lean_nat_dec_lt(v_i_642_, v___x_636_);
if (v___x_643_ == 0)
{
lean_dec(v_i_642_);
lean_dec_ref(v_origin_634_);
return v_headers_633_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_644_ = l_Std_Http_URI_Origin_hostHeader(v_origin_634_);
v___x_645_ = l_Std_Http_Header_Value_ofString_x21(v___x_644_);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_641_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = lean_array_fset(v_headers_633_, v_i_642_, v___x_646_);
lean_dec(v_i_642_);
return v___x_647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1(lean_object* v_00_u03b2_648_, lean_object* v_map_649_, lean_object* v_key_650_, lean_object* v_x_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg(v_map_649_, v_key_650_, v_x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___boxed(lean_object* v_00_u03b2_653_, lean_object* v_map_654_, lean_object* v_key_655_, lean_object* v_x_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1(v_00_u03b2_653_, v_map_654_, v_key_655_, v_x_656_);
lean_dec_ref(v_key_655_);
lean_dec_ref(v_map_654_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(lean_object* v_x_658_){
_start:
{
switch(lean_obj_tag(v_x_658_))
{
case 0:
{
lean_object* v_query_659_; 
v_query_659_ = lean_ctor_get(v_x_658_, 1);
lean_inc(v_query_659_);
return v_query_659_;
}
case 1:
{
lean_object* v_uri_660_; lean_object* v_query_661_; 
v_uri_660_ = lean_ctor_get(v_x_658_, 0);
v_query_661_ = lean_ctor_get(v_uri_660_, 3);
lean_inc(v_query_661_);
return v_query_661_;
}
default: 
{
lean_object* v___x_662_; 
v___x_662_ = lean_box(0);
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f___boxed(lean_object* v_x_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v_x_663_);
lean_dec(v_x_663_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolvedPath(lean_object* v_path_665_){
_start:
{
lean_object* v___x_666_; lean_object* v_segments_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_675_; 
v___x_666_ = l_Std_Http_URI_Path_normalize(v_path_665_);
v_segments_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_675_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_segments_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
uint8_t v___x_671_; lean_object* v___x_673_; 
v___x_671_ = 1;
if (v_isShared_670_ == 0)
{
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_segments_667_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_ctor_set_uint8(v___x_673_, sizeof(void*)*1, v___x_671_);
return v___x_673_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(lean_object* v_ref_676_, uint8_t v_isCrossOrigin_677_, lean_object* v_basePath_678_, lean_object* v_baseQuery_679_, lean_object* v_currentScheme_680_){
_start:
{
lean_object* v___y_682_; lean_object* v___y_683_; 
if (lean_obj_tag(v_ref_676_) == 0)
{
lean_object* v_uri_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_729_; 
lean_dec_ref(v_currentScheme_680_);
lean_dec(v_baseQuery_679_);
lean_dec_ref(v_basePath_678_);
v_uri_686_ = lean_ctor_get(v_ref_676_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v_ref_676_);
if (v_isSharedCheck_729_ == 0)
{
v___x_688_ = v_ref_676_;
v_isShared_689_ = v_isSharedCheck_729_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_uri_686_);
lean_dec(v_ref_676_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_729_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_scheme_690_; lean_object* v_authority_691_; lean_object* v_path_692_; lean_object* v_query_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_727_; 
v_scheme_690_ = lean_ctor_get(v_uri_686_, 0);
v_authority_691_ = lean_ctor_get(v_uri_686_, 1);
v_path_692_ = lean_ctor_get(v_uri_686_, 2);
v_query_693_ = lean_ctor_get(v_uri_686_, 3);
v_isSharedCheck_727_ = !lean_is_exclusive(v_uri_686_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; 
v_unused_728_ = lean_ctor_get(v_uri_686_, 4);
lean_dec(v_unused_728_);
v___x_695_ = v_uri_686_;
v_isShared_696_ = v_isSharedCheck_727_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_query_693_);
lean_inc(v_path_692_);
lean_inc(v_authority_691_);
lean_inc(v_scheme_690_);
lean_dec(v_uri_686_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_727_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___y_698_; 
if (lean_obj_tag(v_authority_691_) == 0)
{
v___y_698_ = v_authority_691_;
goto v___jp_697_;
}
else
{
lean_object* v_val_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_726_; 
v_val_708_ = lean_ctor_get(v_authority_691_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v_authority_691_);
if (v_isSharedCheck_726_ == 0)
{
v___x_710_ = v_authority_691_;
v_isShared_711_ = v_isSharedCheck_726_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_val_708_);
lean_dec(v_authority_691_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_726_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v_host_712_; lean_object* v_port_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_724_; 
v_host_712_ = lean_ctor_get(v_val_708_, 1);
v_port_713_ = lean_ctor_get(v_val_708_, 2);
v_isSharedCheck_724_ = !lean_is_exclusive(v_val_708_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v_val_708_, 0);
lean_dec(v_unused_725_);
v___x_715_ = v_val_708_;
v_isShared_716_ = v_isSharedCheck_724_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_port_713_);
lean_inc(v_host_712_);
lean_dec(v_val_708_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_724_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = lean_box(0);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_717_);
v___x_719_ = v___x_715_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_host_712_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_port_713_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_719_);
v___x_721_ = v___x_710_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
v___y_698_ = v___x_721_;
goto v___jp_697_;
}
}
}
}
}
v___jp_697_:
{
lean_object* v___x_699_; 
v___x_699_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolvedPath(v_path_692_);
if (v_isCrossOrigin_677_ == 0)
{
lean_object* v___x_700_; 
lean_dec(v___y_698_);
lean_del_object(v___x_695_);
lean_dec_ref(v_scheme_690_);
lean_del_object(v___x_688_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v_query_693_);
return v___x_700_;
}
else
{
lean_object* v___x_701_; lean_object* v_stripped_703_; 
v___x_701_ = lean_box(0);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 4, v___x_701_);
lean_ctor_set(v___x_695_, 2, v___x_699_);
lean_ctor_set(v___x_695_, 1, v___y_698_);
v_stripped_703_ = v___x_695_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_scheme_690_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___y_698_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_query_693_);
lean_ctor_set(v_reuseFailAlloc_707_, 4, v___x_701_);
v_stripped_703_ = v_reuseFailAlloc_707_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_705_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set_tag(v___x_688_, 1);
lean_ctor_set(v___x_688_, 0, v_stripped_703_);
v___x_705_ = v___x_688_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_stripped_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
}
}
else
{
lean_object* v_ref_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_771_; 
v_ref_730_ = lean_ctor_get(v_ref_676_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v_ref_676_);
if (v_isSharedCheck_771_ == 0)
{
v___x_732_ = v_ref_676_;
v_isShared_733_ = v_isSharedCheck_771_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_ref_730_);
lean_dec(v_ref_676_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_771_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v_authority_734_; lean_object* v_path_735_; lean_object* v_query_736_; lean_object* v___y_738_; 
v_authority_734_ = lean_ctor_get(v_ref_730_, 0);
lean_inc(v_authority_734_);
v_path_735_ = lean_ctor_get(v_ref_730_, 1);
lean_inc_ref(v_path_735_);
v_query_736_ = lean_ctor_get(v_ref_730_, 2);
lean_inc(v_query_736_);
lean_dec_ref(v_ref_730_);
if (lean_obj_tag(v_authority_734_) == 0)
{
uint8_t v_absolute_739_; uint8_t v___y_741_; 
lean_del_object(v___x_732_);
lean_dec_ref(v_currentScheme_680_);
v_absolute_739_ = lean_ctor_get_uint8(v_path_735_, sizeof(void*)*1);
if (v_absolute_739_ == 0)
{
uint8_t v___x_744_; 
v___x_744_ = l_Std_Http_URI_Path_isEmpty(v_path_735_);
v___y_741_ = v___x_744_;
goto v___jp_740_;
}
else
{
uint8_t v___x_745_; 
v___x_745_ = 0;
v___y_741_ = v___x_745_;
goto v___jp_740_;
}
v___jp_740_:
{
if (v_absolute_739_ == 0)
{
if (v___y_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec(v_baseQuery_679_);
v___x_742_ = l_Std_Http_URI_Path_parent(v_basePath_678_);
v___x_743_ = l_Std_Http_URI_Path_join(v___x_742_, v_path_735_);
lean_dec_ref(v_path_735_);
v___y_682_ = v___x_743_;
v___y_683_ = v_query_736_;
goto v___jp_681_;
}
else
{
lean_dec_ref(v_path_735_);
v___y_738_ = v_basePath_678_;
goto v___jp_737_;
}
}
else
{
lean_dec_ref(v_basePath_678_);
if (v___y_741_ == 0)
{
lean_dec(v_baseQuery_679_);
v___y_682_ = v_path_735_;
v___y_683_ = v_query_736_;
goto v___jp_681_;
}
else
{
v___y_738_ = v_path_735_;
goto v___jp_737_;
}
}
}
}
else
{
lean_object* v_val_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_baseQuery_679_);
lean_dec_ref(v_basePath_678_);
v_val_746_ = lean_ctor_get(v_authority_734_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v_authority_734_);
if (v_isSharedCheck_770_ == 0)
{
v___x_748_ = v_authority_734_;
v_isShared_749_ = v_isSharedCheck_770_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_val_746_);
lean_dec(v_authority_734_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_770_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v_path_750_; 
v_path_750_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolvedPath(v_path_735_);
if (v_isCrossOrigin_677_ == 0)
{
lean_object* v___x_751_; 
lean_del_object(v___x_748_);
lean_dec(v_val_746_);
lean_del_object(v___x_732_);
lean_dec_ref(v_currentScheme_680_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v_path_750_);
lean_ctor_set(v___x_751_, 1, v_query_736_);
return v___x_751_;
}
else
{
lean_object* v_host_752_; lean_object* v_port_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_768_; 
v_host_752_ = lean_ctor_get(v_val_746_, 1);
v_port_753_ = lean_ctor_get(v_val_746_, 2);
v_isSharedCheck_768_ = !lean_is_exclusive(v_val_746_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v_val_746_, 0);
lean_dec(v_unused_769_);
v___x_755_ = v_val_746_;
v_isShared_756_ = v_isSharedCheck_768_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_port_753_);
lean_inc(v_host_752_);
lean_dec(v_val_746_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_768_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v_stripped_759_; 
v___x_757_ = lean_box(0);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_757_);
v_stripped_759_ = v___x_755_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_host_752_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_port_753_);
v_stripped_759_ = v_reuseFailAlloc_767_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_761_; 
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v_stripped_759_);
v___x_761_ = v___x_748_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_stripped_759_);
v___x_761_ = v_reuseFailAlloc_766_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v_af_762_; lean_object* v___x_764_; 
v_af_762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_af_762_, 0, v_currentScheme_680_);
lean_ctor_set(v_af_762_, 1, v___x_761_);
lean_ctor_set(v_af_762_, 2, v_path_750_);
lean_ctor_set(v_af_762_, 3, v_query_736_);
lean_ctor_set(v_af_762_, 4, v___x_757_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v_af_762_);
v___x_764_ = v___x_732_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_af_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
}
}
v___jp_737_:
{
if (lean_obj_tag(v_query_736_) == 0)
{
v___y_682_ = v___y_738_;
v___y_683_ = v_baseQuery_679_;
goto v___jp_681_;
}
else
{
lean_dec(v_baseQuery_679_);
v___y_682_ = v___y_738_;
v___y_683_ = v_query_736_;
goto v___jp_681_;
}
}
}
}
v___jp_681_:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolvedPath(v___y_682_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v___y_683_);
return v___x_685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget___boxed(lean_object* v_ref_772_, lean_object* v_isCrossOrigin_773_, lean_object* v_basePath_774_, lean_object* v_baseQuery_775_, lean_object* v_currentScheme_776_){
_start:
{
uint8_t v_isCrossOrigin_boxed_777_; lean_object* v_res_778_; 
v_isCrossOrigin_boxed_777_ = lean_unbox(v_isCrossOrigin_773_);
v_res_778_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v_ref_772_, v_isCrossOrigin_boxed_777_, v_basePath_774_, v_baseQuery_775_, v_currentScheme_776_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0(lean_object* v___x_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Std_Http_URI_Parser_parseURIReference(v___x_782_, v___y_783_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_pos_785_; lean_object* v_array_786_; lean_object* v_idx_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_pos_785_ = lean_ctor_get(v___x_784_, 0);
v_array_786_ = lean_ctor_get(v_pos_785_, 0);
v_idx_787_ = lean_ctor_get(v_pos_785_, 1);
v___x_788_ = lean_byte_array_size(v_array_786_);
v___x_789_ = lean_nat_dec_lt(v_idx_787_, v___x_788_);
if (v___x_789_ == 0)
{
return v___x_784_;
}
else
{
lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
lean_inc(v_pos_785_);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; lean_object* v_unused_799_; 
v_unused_798_ = lean_ctor_get(v___x_784_, 1);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v___x_784_, 0);
lean_dec(v_unused_799_);
v___x_791_ = v___x_784_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_dec(v___x_784_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1));
if (v_isShared_792_ == 0)
{
lean_ctor_set_tag(v___x_791_, 1);
lean_ctor_set(v___x_791_, 1, v___x_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_pos_785_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg(lean_object* v_map_800_, lean_object* v_key_801_, lean_object* v_i_802_){
_start:
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = lean_array_get_size(v_map_800_);
v___x_804_ = lean_nat_dec_lt(v_i_802_, v___x_803_);
if (v___x_804_ == 0)
{
lean_dec(v_i_802_);
return v___x_803_;
}
else
{
lean_object* v___x_805_; lean_object* v_fst_806_; uint8_t v___x_807_; 
v___x_805_ = lean_array_fget_borrowed(v_map_800_, v_i_802_);
v_fst_806_ = lean_ctor_get(v___x_805_, 0);
v___x_807_ = lean_string_dec_eq(v_fst_806_, v_key_801_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_unsigned_to_nat(1u);
v___x_809_ = lean_nat_add(v_i_802_, v___x_808_);
lean_dec(v_i_802_);
v_i_802_ = v___x_809_;
goto _start;
}
else
{
return v_i_802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg___boxed(lean_object* v_map_811_, lean_object* v_key_812_, lean_object* v_i_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg(v_map_811_, v_key_812_, v_i_813_);
lean_dec_ref(v_key_812_);
lean_dec_ref(v_map_811_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect(lean_object* v_current_824_, lean_object* v_request_825_, uint8_t v_bodyReplayable_826_, lean_object* v_status_827_, lean_object* v_responseHeaders_828_){
_start:
{
uint16_t v___x_829_; uint16_t v___x_830_; uint8_t v___x_831_; 
v___x_829_ = 300;
v___x_830_ = l_Std_Http_Status_toCode(v_status_827_);
v___x_831_ = lean_uint16_dec_le(v___x_829_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
lean_dec_ref(v_current_824_);
v___x_832_ = lean_box(0);
return v___x_832_;
}
else
{
uint16_t v___x_833_; uint8_t v___x_834_; 
v___x_833_ = 400;
v___x_834_ = lean_uint16_dec_lt(v___x_830_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
lean_dec_ref(v_current_824_);
v___x_835_ = lean_box(0);
return v___x_835_;
}
else
{
uint8_t v_method_836_; lean_object* v_uri_837_; lean_object* v_headers_838_; uint8_t v___x_839_; uint8_t v___x_840_; 
v_method_836_ = lean_ctor_get_uint8(v_request_825_, sizeof(void*)*2);
v_uri_837_ = lean_ctor_get(v_request_825_, 0);
v_headers_838_ = lean_ctor_get(v_request_825_, 1);
v___x_839_ = 5;
v___x_840_ = l_Std_Http_instBEqMethod_beq(v_method_836_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = lean_box(19);
v___x_842_ = l_Std_Http_instBEqStatus_beq(v_status_827_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_843_ = lean_box(20);
v___x_844_ = l_Std_Http_instBEqStatus_beq(v_status_827_, v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = lean_box(18);
v___x_846_ = l_Std_Http_instBEqStatus_beq(v_status_827_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = lean_box(14);
v___x_848_ = l_Std_Http_instBEqStatus_beq(v_status_827_, v___x_847_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v_i_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_849_ = l_Std_Http_Header_Name_location;
v___x_850_ = lean_unsigned_to_nat(0u);
v_i_851_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg(v_responseHeaders_828_, v___x_849_, v___x_850_);
v___x_852_ = lean_array_get_size(v_responseHeaders_828_);
v___x_853_ = lean_nat_dec_lt(v_i_851_, v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; 
lean_dec(v_i_851_);
lean_dec_ref(v_current_824_);
v___x_854_ = lean_box(0);
return v___x_854_;
}
else
{
lean_object* v___x_855_; lean_object* v_snd_856_; lean_object* v___f_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_855_ = lean_array_fget_borrowed(v_responseHeaders_828_, v_i_851_);
lean_dec(v_i_851_);
v_snd_856_ = lean_ctor_get(v___x_855_, 1);
v___f_857_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__1));
lean_inc(v_snd_856_);
v___x_858_ = lean_string_to_utf8(v_snd_856_);
v___x_859_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_857_, v___x_858_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v___x_860_; 
lean_dec_ref_known(v___x_859_, 1);
lean_dec_ref(v_current_824_);
v___x_860_ = lean_box(0);
return v___x_860_;
}
else
{
lean_object* v_a_861_; lean_object* v___x_862_; 
v_a_861_ = lean_ctor_get(v___x_859_, 0);
lean_inc_n(v_a_861_, 2);
lean_dec_ref_known(v___x_859_, 1);
lean_inc_ref(v_current_824_);
v___x_862_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(v_current_824_, v_a_861_);
if (lean_obj_tag(v___x_862_) == 1)
{
lean_object* v_val_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_938_; 
v_val_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_938_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_938_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_val_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_938_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_scheme_867_; uint8_t v_newMethod_868_; lean_object* v___y_870_; uint8_t v___y_871_; uint8_t v___y_872_; lean_object* v___y_882_; uint8_t v___y_883_; lean_object* v___y_886_; uint8_t v___y_887_; uint8_t v___y_888_; lean_object* v___y_895_; uint8_t v___y_896_; uint8_t v___y_897_; uint8_t v___y_898_; lean_object* v___y_902_; uint8_t v___y_903_; uint8_t v___y_904_; uint8_t v___y_905_; lean_object* v___y_909_; uint8_t v___y_910_; uint8_t v___y_911_; uint8_t v___y_912_; uint8_t v___y_916_; uint8_t v___y_917_; uint8_t v___y_918_; lean_object* v___y_919_; uint8_t v___y_921_; uint8_t v___y_922_; uint8_t v___y_923_; uint8_t v___y_927_; uint8_t v___y_928_; uint8_t v___y_931_; lean_object* v___x_933_; uint8_t v___x_934_; 
v_scheme_867_ = lean_ctor_get(v_val_863_, 0);
v_newMethod_868_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_method_836_, v_status_827_);
v___x_933_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__2));
v___x_934_ = lean_string_dec_eq(v_scheme_867_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_935_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__3));
v___x_936_ = lean_string_dec_eq(v_scheme_867_, v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; 
lean_del_object(v___x_865_);
lean_dec(v_val_863_);
lean_dec(v_a_861_);
lean_dec_ref(v_current_824_);
v___x_937_ = lean_box(0);
return v___x_937_;
}
else
{
v___y_931_ = v___x_848_;
goto v___jp_930_;
}
}
else
{
v___y_931_ = v___x_848_;
goto v___jp_930_;
}
v___jp_869_:
{
lean_object* v_scheme_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v_rewrittenTarget_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v_scheme_873_ = lean_ctor_get(v_current_824_, 0);
lean_inc_ref(v_scheme_873_);
lean_dec_ref(v_current_824_);
v___x_874_ = l_Std_Http_RequestTarget_pathOrRoot(v_uri_837_);
v___x_875_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v_uri_837_);
v_rewrittenTarget_876_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v_a_861_, v___y_871_, v___x_874_, v___x_875_, v_scheme_873_);
v___x_877_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_877_, 0, v_val_863_);
lean_ctor_set(v___x_877_, 1, v_rewrittenTarget_876_);
lean_ctor_set(v___x_877_, 2, v___y_870_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*3, v_newMethod_868_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*3 + 1, v___y_872_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*3 + 2, v___y_871_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_877_);
v___x_879_ = v___x_865_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
v___jp_881_:
{
uint8_t v___x_884_; 
v___x_884_ = 0;
v___y_870_ = v___y_882_;
v___y_871_ = v___y_883_;
v___y_872_ = v___x_884_;
goto v___jp_869_;
}
v___jp_885_:
{
uint8_t v___x_889_; uint8_t v___x_890_; 
v___x_889_ = 8;
v___x_890_ = l_Std_Http_instBEqMethod_beq(v_newMethod_868_, v___x_889_);
if (v___x_890_ == 0)
{
uint8_t v___x_891_; uint8_t v___x_892_; 
v___x_891_ = 9;
v___x_892_ = l_Std_Http_instBEqMethod_beq(v_newMethod_868_, v___x_891_);
if (v___x_892_ == 0)
{
if (v___y_888_ == 0)
{
uint8_t v___x_893_; 
v___x_893_ = 1;
v___y_870_ = v___y_886_;
v___y_871_ = v___y_887_;
v___y_872_ = v___x_893_;
goto v___jp_869_;
}
else
{
v___y_882_ = v___y_886_;
v___y_883_ = v___y_887_;
goto v___jp_881_;
}
}
else
{
v___y_882_ = v___y_886_;
v___y_883_ = v___y_887_;
goto v___jp_881_;
}
}
else
{
v___y_882_ = v___y_886_;
v___y_883_ = v___y_887_;
goto v___jp_881_;
}
}
v___jp_894_:
{
if (v_bodyReplayable_826_ == 0)
{
lean_object* v___x_899_; 
lean_dec_ref(v___y_895_);
lean_del_object(v___x_865_);
lean_dec(v_val_863_);
lean_dec(v_a_861_);
lean_dec_ref(v_current_824_);
v___x_899_ = lean_box(0);
return v___x_899_;
}
else
{
if (v___y_896_ == 0)
{
v___y_886_ = v___y_895_;
v___y_887_ = v___y_897_;
v___y_888_ = v___y_898_;
goto v___jp_885_;
}
else
{
lean_object* v___x_900_; 
lean_dec_ref(v___y_895_);
lean_del_object(v___x_865_);
lean_dec(v_val_863_);
lean_dec(v_a_861_);
lean_dec_ref(v_current_824_);
v___x_900_ = lean_box(0);
return v___x_900_;
}
}
}
v___jp_901_:
{
uint8_t v___x_906_; uint8_t v___x_907_; 
v___x_906_ = 9;
v___x_907_ = l_Std_Http_instBEqMethod_beq(v_newMethod_868_, v___x_906_);
if (v___x_907_ == 0)
{
v___y_895_ = v___y_902_;
v___y_896_ = v___y_903_;
v___y_897_ = v___y_904_;
v___y_898_ = v___y_905_;
goto v___jp_894_;
}
else
{
if (v___y_903_ == 0)
{
v___y_886_ = v___y_902_;
v___y_887_ = v___y_904_;
v___y_888_ = v___y_905_;
goto v___jp_885_;
}
else
{
v___y_895_ = v___y_902_;
v___y_896_ = v___y_903_;
v___y_897_ = v___y_904_;
v___y_898_ = v___y_905_;
goto v___jp_894_;
}
}
}
v___jp_908_:
{
uint8_t v___x_913_; uint8_t v___x_914_; 
v___x_913_ = 8;
v___x_914_ = l_Std_Http_instBEqMethod_beq(v_newMethod_868_, v___x_913_);
if (v___x_914_ == 0)
{
v___y_902_ = v___y_909_;
v___y_903_ = v___y_910_;
v___y_904_ = v___y_911_;
v___y_905_ = v___y_912_;
goto v___jp_901_;
}
else
{
if (v___y_910_ == 0)
{
v___y_886_ = v___y_909_;
v___y_887_ = v___y_911_;
v___y_888_ = v___y_912_;
goto v___jp_885_;
}
else
{
v___y_902_ = v___y_909_;
v___y_903_ = v___y_910_;
v___y_904_ = v___y_911_;
v___y_905_ = v___y_912_;
goto v___jp_901_;
}
}
}
v___jp_915_:
{
if (v___y_918_ == 0)
{
v___y_909_ = v___y_919_;
v___y_910_ = v___y_916_;
v___y_911_ = v___y_917_;
v___y_912_ = v___y_918_;
goto v___jp_908_;
}
else
{
if (v___y_916_ == 0)
{
v___y_886_ = v___y_919_;
v___y_887_ = v___y_917_;
v___y_888_ = v___y_918_;
goto v___jp_885_;
}
else
{
v___y_909_ = v___y_919_;
v___y_910_ = v___y_916_;
v___y_911_ = v___y_917_;
v___y_912_ = v___y_918_;
goto v___jp_908_;
}
}
}
v___jp_920_:
{
lean_object* v_scrubbed_924_; 
v_scrubbed_924_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v_headers_838_, v___y_922_, v___y_923_);
if (v___y_922_ == 0)
{
v___y_916_ = v___y_921_;
v___y_917_ = v___y_922_;
v___y_918_ = v___y_923_;
v___y_919_ = v_scrubbed_924_;
goto v___jp_915_;
}
else
{
lean_object* v___x_925_; 
lean_inc(v_val_863_);
v___x_925_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(v_scrubbed_924_, v_val_863_);
v___y_916_ = v___y_921_;
v___y_917_ = v___y_922_;
v___y_918_ = v___y_923_;
v___y_919_ = v___x_925_;
goto v___jp_915_;
}
}
v___jp_926_:
{
uint8_t v___x_929_; 
v___x_929_ = l_Std_Http_instBEqMethod_beq(v_newMethod_868_, v_method_836_);
if (v___x_929_ == 0)
{
v___y_921_ = v___y_927_;
v___y_922_ = v___y_928_;
v___y_923_ = v___x_853_;
goto v___jp_920_;
}
else
{
v___y_921_ = v___y_927_;
v___y_922_ = v___y_928_;
v___y_923_ = v___y_927_;
goto v___jp_920_;
}
}
v___jp_930_:
{
uint8_t v___x_932_; 
v___x_932_ = l_Std_Http_URI_instBEqOrigin_beq(v_val_863_, v_current_824_);
if (v___x_932_ == 0)
{
v___y_927_ = v___y_931_;
v___y_928_ = v___x_853_;
goto v___jp_926_;
}
else
{
v___y_927_ = v___y_931_;
v___y_928_ = v___y_931_;
goto v___jp_926_;
}
}
}
}
else
{
lean_object* v___x_939_; 
lean_dec(v___x_862_);
lean_dec(v_a_861_);
lean_dec_ref(v_current_824_);
v___x_939_ = lean_box(0);
return v___x_939_;
}
}
}
}
else
{
lean_object* v___x_940_; 
lean_dec_ref(v_current_824_);
v___x_940_ = lean_box(0);
return v___x_940_;
}
}
else
{
lean_object* v___x_941_; 
lean_dec_ref(v_current_824_);
v___x_941_ = lean_box(0);
return v___x_941_;
}
}
else
{
lean_object* v___x_942_; 
lean_dec_ref(v_current_824_);
v___x_942_ = lean_box(0);
return v___x_942_;
}
}
else
{
lean_object* v___x_943_; 
lean_dec_ref(v_current_824_);
v___x_943_ = lean_box(0);
return v___x_943_;
}
}
else
{
lean_object* v___x_944_; 
lean_dec_ref(v_current_824_);
v___x_944_ = lean_box(0);
return v___x_944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___boxed(lean_object* v_current_945_, lean_object* v_request_946_, lean_object* v_bodyReplayable_947_, lean_object* v_status_948_, lean_object* v_responseHeaders_949_){
_start:
{
uint8_t v_bodyReplayable_boxed_950_; lean_object* v_res_951_; 
v_bodyReplayable_boxed_950_ = lean_unbox(v_bodyReplayable_947_);
v_res_951_ = l_Std_Http_Protocol_H1_decideRedirect(v_current_945_, v_request_946_, v_bodyReplayable_boxed_950_, v_status_948_, v_responseHeaders_949_);
lean_dec_ref(v_responseHeaders_949_);
lean_dec(v_status_948_);
lean_dec_ref(v_request_946_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0(lean_object* v_00_u03b2_952_, lean_object* v_map_953_, lean_object* v_key_954_, lean_object* v_i_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg(v_map_953_, v_key_954_, v_i_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___boxed(lean_object* v_00_u03b2_957_, lean_object* v_map_958_, lean_object* v_key_959_, lean_object* v_i_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0(v_00_u03b2_957_, v_map_958_, v_key_959_, v_i_960_);
lean_dec_ref(v_key_959_);
lean_dec_ref(v_map_958_);
return v_res_961_;
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
