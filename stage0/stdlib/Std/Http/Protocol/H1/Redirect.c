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
lean_object* l_Std_Http_Header_Connection_parse(lean_object*);
lean_object* l_Std_Http_URI_Parser_parseURIReference(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
extern lean_object* l_Std_Http_Header_Name_ifModifiedSince;
extern lean_object* l_Std_Http_Header_Name_ifNoneMatch;
lean_object* l_Std_Http_RequestTarget_pathOrRoot(lean_object*);
lean_object* l_Std_Http_URI_Path_normalize(lean_object*);
uint8_t l_Std_Http_URI_Path_isEmpty(lean_object*);
lean_object* l_Std_Http_URI_Path_parent(lean_object*);
lean_object* l_Std_Http_URI_Path_join(lean_object*, lean_object*);
uint8_t l_Std_Http_instBEqMethod_beq(uint8_t, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
extern lean_object* l_Std_Http_Header_Name_keepAlive;
extern lean_object* l_Std_Http_Header_Name_referer;
extern lean_object* l_Std_Http_Header_Name_cookie;
extern lean_object* l_Std_Http_Header_Name_authorization;
uint16_t l_Std_Http_Status_toCode(lean_object*);
uint8_t lean_uint16_dec_le(uint16_t, uint16_t);
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
uint8_t l_Std_Http_URI_instBEqOrigin_beq(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_location;
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
uint8_t l_Std_Http_instBEqVersion_beq(uint8_t, uint8_t);
uint8_t l_Std_Http_instBEqStatus_beq(lean_object*, lean_object*);
uint8_t l_Std_Http_Method_isSafe(uint8_t);
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
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_decideRedirect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "https"};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_decideRedirect___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*9 + 0, .m_other = 9, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(253) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(256) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(128) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(100) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___closed__1_value;
static const lean_closure_object l_Std_Http_Protocol_H1_decideRedirect___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_decideRedirect___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___closed__1_value)} };
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___closed__2_value;
static const lean_string_object l_Std_Http_Protocol_H1_decideRedirect___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "http"};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(uint8_t v_originalMethod_334_, uint8_t v_responseVersion_335_, lean_object* v_x_336_){
_start:
{
switch(lean_obj_tag(v_x_336_))
{
case 17:
{
uint8_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = 9;
v___x_344_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_334_, v___x_343_);
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
goto v___jp_337_;
}
case 16:
{
goto v___jp_337_;
}
default: 
{
return v_originalMethod_334_;
}
}
v___jp_337_:
{
uint8_t v___x_338_; uint8_t v___x_339_; 
v___x_338_ = 23;
v___x_339_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_334_, v___x_338_);
if (v___x_339_ == 0)
{
return v_originalMethod_334_;
}
else
{
uint8_t v___x_340_; uint8_t v___x_341_; 
v___x_340_ = 0;
v___x_341_ = l_Std_Http_instBEqVersion_beq(v_responseVersion_335_, v___x_340_);
if (v___x_341_ == 0)
{
uint8_t v___x_342_; 
v___x_342_ = 8;
return v___x_342_;
}
else
{
return v_originalMethod_334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod___boxed(lean_object* v_originalMethod_346_, lean_object* v_responseVersion_347_, lean_object* v_x_348_){
_start:
{
uint8_t v_originalMethod_boxed_349_; uint8_t v_responseVersion_boxed_350_; uint8_t v_res_351_; lean_object* v_r_352_; 
v_originalMethod_boxed_349_ = lean_unbox(v_originalMethod_346_);
v_responseVersion_boxed_350_ = lean_unbox(v_responseVersion_347_);
v_res_351_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_originalMethod_boxed_349_, v_responseVersion_boxed_350_, v_x_348_);
lean_dec(v_x_348_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_353_ = l_Std_Http_Header_Name_transferEncoding;
v___x_354_ = l_Std_Http_Header_Name_keepAlive;
v___x_355_ = l_Std_Http_Header_Name_connection;
v___x_356_ = lean_unsigned_to_nat(3u);
v___x_357_ = lean_mk_empty_array_with_capacity(v___x_356_);
v___x_358_ = lean_array_push(v___x_357_, v___x_355_);
v___x_359_ = lean_array_push(v___x_358_, v___x_354_);
v___x_360_ = lean_array_push(v___x_359_, v___x_353_);
return v___x_360_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders(void){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(lean_object* v_as_362_, size_t v_i_363_, size_t v_stop_364_, lean_object* v_b_365_){
_start:
{
lean_object* v___y_367_; uint8_t v___x_371_; 
v___x_371_ = lean_usize_dec_eq(v_i_363_, v_stop_364_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_array_uget_borrowed(v_as_362_, v_i_363_);
lean_inc(v___x_372_);
v___x_373_ = l_Std_Http_Header_Name_ofString_x3f(v___x_372_);
if (lean_obj_tag(v___x_373_) == 0)
{
v___y_367_ = v_b_365_;
goto v___jp_366_;
}
else
{
lean_object* v_val_374_; lean_object* v___x_375_; 
v_val_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_val_374_);
lean_dec_ref_known(v___x_373_, 1);
v___x_375_ = lean_array_push(v_b_365_, v_val_374_);
v___y_367_ = v___x_375_;
goto v___jp_366_;
}
}
else
{
return v_b_365_;
}
v___jp_366_:
{
size_t v___x_368_; size_t v___x_369_; 
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_add(v_i_363_, v___x_368_);
v_i_363_ = v___x_369_;
v_b_365_ = v___y_367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0___boxed(lean_object* v_as_376_, lean_object* v_i_377_, lean_object* v_stop_378_, lean_object* v_b_379_){
_start:
{
size_t v_i_boxed_380_; size_t v_stop_boxed_381_; lean_object* v_res_382_; 
v_i_boxed_380_ = lean_unbox_usize(v_i_377_);
lean_dec(v_i_377_);
v_stop_boxed_381_ = lean_unbox_usize(v_stop_378_);
lean_dec(v_stop_378_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_as_376_, v_i_boxed_380_, v_stop_boxed_381_, v_b_379_);
lean_dec_ref(v_as_376_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(lean_object* v_as_383_, size_t v_i_384_, size_t v_stop_385_, lean_object* v_b_386_){
_start:
{
lean_object* v___y_388_; uint8_t v___x_392_; 
v___x_392_ = lean_usize_dec_eq(v_i_384_, v_stop_385_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_array_uget_borrowed(v_as_383_, v_i_384_);
lean_inc(v___x_393_);
v___x_394_ = l_Std_Http_Header_Connection_parse(v___x_393_);
if (lean_obj_tag(v___x_394_) == 0)
{
v___y_388_ = v_b_386_;
goto v___jp_387_;
}
else
{
lean_object* v_val_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_val_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v___x_394_, 1);
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = lean_array_get_size(v_val_395_);
v___x_398_ = lean_nat_dec_lt(v___x_396_, v___x_397_);
if (v___x_398_ == 0)
{
lean_dec(v_val_395_);
v___y_388_ = v_b_386_;
goto v___jp_387_;
}
else
{
size_t v___x_399_; size_t v___x_400_; lean_object* v___x_401_; 
v___x_399_ = ((size_t)0ULL);
v___x_400_ = lean_usize_of_nat(v___x_397_);
v___x_401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_val_395_, v___x_399_, v___x_400_, v_b_386_);
lean_dec(v_val_395_);
v___y_388_ = v___x_401_;
goto v___jp_387_;
}
}
}
else
{
return v_b_386_;
}
v___jp_387_:
{
size_t v___x_389_; size_t v___x_390_; 
v___x_389_ = ((size_t)1ULL);
v___x_390_ = lean_usize_add(v_i_384_, v___x_389_);
v_i_384_ = v___x_390_;
v_b_386_ = v___y_388_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___boxed(lean_object* v_as_402_, lean_object* v_i_403_, lean_object* v_stop_404_, lean_object* v_b_405_){
_start:
{
size_t v_i_boxed_406_; size_t v_stop_boxed_407_; lean_object* v_res_408_; 
v_i_boxed_406_ = lean_unbox_usize(v_i_403_);
lean_dec(v_i_403_);
v_stop_boxed_407_ = lean_unbox_usize(v_stop_404_);
lean_dec(v_stop_404_);
v_res_408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(v_as_402_, v_i_boxed_406_, v_stop_boxed_407_, v_b_405_);
lean_dec_ref(v_as_402_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(lean_object* v_as_409_, size_t v_i_410_, size_t v_stop_411_, lean_object* v_b_412_){
_start:
{
lean_object* v___y_414_; uint8_t v___x_418_; 
v___x_418_ = lean_usize_dec_eq(v_i_410_, v_stop_411_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v_fst_420_; lean_object* v_snd_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_419_ = lean_array_uget_borrowed(v_as_409_, v_i_410_);
v_fst_420_ = lean_ctor_get(v___x_419_, 0);
v_snd_421_ = lean_ctor_get(v___x_419_, 1);
v___x_422_ = l_Std_Http_Header_Name_connection;
v___x_423_ = lean_string_dec_eq(v_fst_420_, v___x_422_);
if (v___x_423_ == 0)
{
v___y_414_ = v_b_412_;
goto v___jp_413_;
}
else
{
lean_object* v___x_424_; 
lean_inc(v_snd_421_);
v___x_424_ = lean_array_push(v_b_412_, v_snd_421_);
v___y_414_ = v___x_424_;
goto v___jp_413_;
}
}
else
{
return v_b_412_;
}
v___jp_413_:
{
size_t v___x_415_; size_t v___x_416_; 
v___x_415_ = ((size_t)1ULL);
v___x_416_ = lean_usize_add(v_i_410_, v___x_415_);
v_i_410_ = v___x_416_;
v_b_412_ = v___y_414_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___boxed(lean_object* v_as_425_, lean_object* v_i_426_, lean_object* v_stop_427_, lean_object* v_b_428_){
_start:
{
size_t v_i_boxed_429_; size_t v_stop_boxed_430_; lean_object* v_res_431_; 
v_i_boxed_429_ = lean_unbox_usize(v_i_426_);
lean_dec(v_i_426_);
v_stop_boxed_430_ = lean_unbox_usize(v_stop_427_);
lean_dec(v_stop_427_);
v_res_431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(v_as_425_, v_i_boxed_429_, v_stop_boxed_430_, v_b_428_);
lean_dec_ref(v_as_425_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(lean_object* v_headers_434_){
_start:
{
lean_object* v___y_436_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___x_448_ = lean_array_get_size(v_headers_434_);
v___x_449_ = lean_nat_dec_lt(v___x_446_, v___x_448_);
if (v___x_449_ == 0)
{
v___y_436_ = v___x_447_;
goto v___jp_435_;
}
else
{
size_t v___x_450_; size_t v___x_451_; lean_object* v___x_452_; 
v___x_450_ = ((size_t)0ULL);
v___x_451_ = lean_usize_of_nat(v___x_448_);
v___x_452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(v_headers_434_, v___x_450_, v___x_451_, v___x_447_);
v___y_436_ = v___x_452_;
goto v___jp_435_;
}
v___jp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_437_ = lean_array_get_size(v___y_436_);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_nat_dec_eq(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___x_441_ = lean_nat_dec_lt(v___x_438_, v___x_437_);
if (v___x_441_ == 0)
{
lean_dec_ref(v___y_436_);
return v___x_440_;
}
else
{
size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
v___x_442_ = ((size_t)0ULL);
v___x_443_ = lean_usize_of_nat(v___x_437_);
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(v___y_436_, v___x_442_, v___x_443_, v___x_440_);
lean_dec_ref(v___y_436_);
return v___x_444_;
}
}
else
{
lean_object* v___x_445_; 
lean_dec_ref(v___y_436_);
v___x_445_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
return v___x_445_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___boxed(lean_object* v_headers_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_453_);
lean_dec_ref(v_headers_453_);
return v_res_454_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_455_ = l_Std_Http_Header_Name_proxyAuthorization;
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = lean_mk_empty_array_with_capacity(v___x_456_);
v___x_458_ = lean_array_push(v___x_457_, v___x_455_);
return v___x_458_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders(void){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0);
return v___x_459_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_460_ = l_Std_Http_Header_Name_referer;
v___x_461_ = l_Std_Http_Header_Name_cookie;
v___x_462_ = l_Std_Http_Header_Name_authorization;
v___x_463_ = lean_unsigned_to_nat(3u);
v___x_464_ = lean_mk_empty_array_with_capacity(v___x_463_);
v___x_465_ = lean_array_push(v___x_464_, v___x_462_);
v___x_466_ = lean_array_push(v___x_465_, v___x_461_);
v___x_467_ = lean_array_push(v___x_466_, v___x_460_);
return v___x_467_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders(void){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0);
return v___x_468_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_469_ = l_Std_Http_Header_Name_ifModifiedSince;
v___x_470_ = l_Std_Http_Header_Name_ifNoneMatch;
v___x_471_ = lean_unsigned_to_nat(2u);
v___x_472_ = lean_mk_empty_array_with_capacity(v___x_471_);
v___x_473_ = lean_array_push(v___x_472_, v___x_470_);
v___x_474_ = lean_array_push(v___x_473_, v___x_469_);
return v___x_474_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders(void){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0);
return v___x_475_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_476_ = l_Std_Http_Header_Name_lastModified;
v___x_477_ = l_Std_Http_Header_Name_contentLocation;
v___x_478_ = l_Std_Http_Header_Name_contentLanguage;
v___x_479_ = l_Std_Http_Header_Name_contentEncoding;
v___x_480_ = l_Std_Http_Header_Name_contentLength;
v___x_481_ = l_Std_Http_Header_Name_contentType;
v___x_482_ = lean_unsigned_to_nat(6u);
v___x_483_ = lean_mk_empty_array_with_capacity(v___x_482_);
v___x_484_ = lean_array_push(v___x_483_, v___x_481_);
v___x_485_ = lean_array_push(v___x_484_, v___x_480_);
v___x_486_ = lean_array_push(v___x_485_, v___x_479_);
v___x_487_ = lean_array_push(v___x_486_, v___x_478_);
v___x_488_ = lean_array_push(v___x_487_, v___x_477_);
v___x_489_ = lean_array_push(v___x_488_, v___x_476_);
return v___x_489_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders(void){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0);
return v___x_490_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(lean_object* v_a_491_, lean_object* v_as_492_, size_t v_i_493_, size_t v_stop_494_){
_start:
{
uint8_t v___x_495_; 
v___x_495_ = lean_usize_dec_eq(v_i_493_, v_stop_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = lean_array_uget_borrowed(v_as_492_, v_i_493_);
v___x_497_ = lean_string_dec_eq(v_a_491_, v___x_496_);
if (v___x_497_ == 0)
{
size_t v___x_498_; size_t v___x_499_; 
v___x_498_ = ((size_t)1ULL);
v___x_499_ = lean_usize_add(v_i_493_, v___x_498_);
v_i_493_ = v___x_499_;
goto _start;
}
else
{
return v___x_497_;
}
}
else
{
uint8_t v___x_501_; 
v___x_501_ = 0;
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___boxed(lean_object* v_a_502_, lean_object* v_as_503_, lean_object* v_i_504_, lean_object* v_stop_505_){
_start:
{
size_t v_i_boxed_506_; size_t v_stop_boxed_507_; uint8_t v_res_508_; lean_object* v_r_509_; 
v_i_boxed_506_ = lean_unbox_usize(v_i_504_);
lean_dec(v_i_504_);
v_stop_boxed_507_ = lean_unbox_usize(v_stop_505_);
lean_dec(v_stop_505_);
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_a_502_, v_as_503_, v_i_boxed_506_, v_stop_boxed_507_);
lean_dec_ref(v_as_503_);
lean_dec_ref(v_a_502_);
v_r_509_ = lean_box(v_res_508_);
return v_r_509_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(lean_object* v_as_510_, lean_object* v_a_511_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = lean_array_get_size(v_as_510_);
v___x_514_ = lean_nat_dec_lt(v___x_512_, v___x_513_);
if (v___x_514_ == 0)
{
return v___x_514_;
}
else
{
size_t v___x_515_; size_t v___x_516_; uint8_t v___x_517_; 
v___x_515_ = ((size_t)0ULL);
v___x_516_ = lean_usize_of_nat(v___x_513_);
v___x_517_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_a_511_, v_as_510_, v___x_515_, v___x_516_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___boxed(lean_object* v_as_518_, lean_object* v_a_519_){
_start:
{
uint8_t v_res_520_; lean_object* v_r_521_; 
v_res_520_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v_as_518_, v_a_519_);
lean_dec_ref(v_a_519_);
lean_dec_ref(v_as_518_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(lean_object* v___y_522_, lean_object* v_as_523_, size_t v_i_524_, size_t v_stop_525_){
_start:
{
uint8_t v___x_526_; 
v___x_526_ = lean_usize_dec_eq(v_i_524_, v_stop_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v_fst_528_; uint8_t v___x_529_; 
v___x_527_ = lean_array_uget_borrowed(v_as_523_, v_i_524_);
v_fst_528_ = lean_ctor_get(v___x_527_, 0);
v___x_529_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v___y_522_, v_fst_528_);
if (v___x_529_ == 0)
{
size_t v___x_530_; size_t v___x_531_; 
v___x_530_ = ((size_t)1ULL);
v___x_531_ = lean_usize_add(v_i_524_, v___x_530_);
v_i_524_ = v___x_531_;
goto _start;
}
else
{
return v___x_529_;
}
}
else
{
uint8_t v___x_533_; 
v___x_533_ = 0;
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1___boxed(lean_object* v___y_534_, lean_object* v_as_535_, lean_object* v_i_536_, lean_object* v_stop_537_){
_start:
{
size_t v_i_boxed_538_; size_t v_stop_boxed_539_; uint8_t v_res_540_; lean_object* v_r_541_; 
v_i_boxed_538_ = lean_unbox_usize(v_i_536_);
lean_dec(v_i_536_);
v_stop_boxed_539_ = lean_unbox_usize(v_stop_537_);
lean_dec(v_stop_537_);
v_res_540_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(v___y_534_, v_as_535_, v_i_boxed_538_, v_stop_boxed_539_);
lean_dec_ref(v_as_535_);
lean_dec_ref(v___y_534_);
v_r_541_ = lean_box(v_res_540_);
return v_r_541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_object* v___y_542_, lean_object* v_as_543_, size_t v_i_544_, size_t v_stop_545_, lean_object* v_b_546_){
_start:
{
lean_object* v___y_548_; uint8_t v___x_552_; 
v___x_552_ = lean_usize_dec_eq(v_i_544_, v_stop_545_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v_fst_554_; uint8_t v___x_555_; 
v___x_553_ = lean_array_uget_borrowed(v_as_543_, v_i_544_);
v_fst_554_ = lean_ctor_get(v___x_553_, 0);
v___x_555_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v___y_542_, v_fst_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
lean_inc(v___x_553_);
v___x_556_ = lean_array_push(v_b_546_, v___x_553_);
v___y_548_ = v___x_556_;
goto v___jp_547_;
}
else
{
v___y_548_ = v_b_546_;
goto v___jp_547_;
}
}
else
{
return v_b_546_;
}
v___jp_547_:
{
size_t v___x_549_; size_t v___x_550_; 
v___x_549_ = ((size_t)1ULL);
v___x_550_ = lean_usize_add(v_i_544_, v___x_549_);
v_i_544_ = v___x_550_;
v_b_546_ = v___y_548_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___boxed(lean_object* v___y_557_, lean_object* v_as_558_, lean_object* v_i_559_, lean_object* v_stop_560_, lean_object* v_b_561_){
_start:
{
size_t v_i_boxed_562_; size_t v_stop_boxed_563_; lean_object* v_res_564_; 
v_i_boxed_562_ = lean_unbox_usize(v_i_559_);
lean_dec(v_i_559_);
v_stop_boxed_563_ = lean_unbox_usize(v_stop_560_);
lean_dec(v_stop_560_);
v_res_564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(v___y_557_, v_as_558_, v_i_boxed_562_, v_stop_boxed_563_, v_b_561_);
lean_dec_ref(v_as_558_);
lean_dec_ref(v___y_557_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(lean_object* v_headers_567_, uint8_t v_isCrossOrigin_568_, uint8_t v_methodChanged_569_){
_start:
{
lean_object* v___y_571_; lean_object* v___y_581_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_afterConnection_588_; 
v___x_586_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders;
v___x_587_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_567_);
v_afterConnection_588_ = l_Array_append___redArg(v___x_586_, v___x_587_);
lean_dec_ref(v___x_587_);
if (v_isCrossOrigin_568_ == 0)
{
v___y_581_ = v_afterConnection_588_;
goto v___jp_580_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_589_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders;
v___x_590_ = l_Array_append___redArg(v_afterConnection_588_, v___x_589_);
v___x_591_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders;
v___x_592_ = l_Array_append___redArg(v___x_590_, v___x_591_);
v___x_593_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_594_ = l_Array_append___redArg(v___x_592_, v___x_593_);
v___y_581_ = v___x_594_;
goto v___jp_580_;
}
v___jp_570_:
{
lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = lean_array_get_size(v_headers_567_);
v___x_574_ = lean_nat_dec_lt(v___x_572_, v___x_573_);
if (v___x_574_ == 0)
{
lean_dec_ref(v___y_571_);
lean_inc_ref(v_headers_567_);
return v_headers_567_;
}
else
{
size_t v___x_575_; size_t v___x_576_; uint8_t v___x_577_; 
v___x_575_ = ((size_t)0ULL);
v___x_576_ = lean_usize_of_nat(v___x_573_);
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(v___y_571_, v_headers_567_, v___x_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_dec_ref(v___y_571_);
lean_inc_ref(v_headers_567_);
return v_headers_567_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___closed__0));
v___x_579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(v___y_571_, v_headers_567_, v___x_575_, v___x_576_, v___x_578_);
lean_dec_ref(v___y_571_);
return v___x_579_;
}
}
}
v___jp_580_:
{
if (v_methodChanged_569_ == 0)
{
v___y_571_ = v___y_581_;
goto v___jp_570_;
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_582_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders;
v___x_583_ = l_Array_append___redArg(v___y_581_, v___x_582_);
v___x_584_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_585_ = l_Array_append___redArg(v___x_583_, v___x_584_);
v___y_571_ = v___x_585_;
goto v___jp_570_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___boxed(lean_object* v_headers_595_, lean_object* v_isCrossOrigin_596_, lean_object* v_methodChanged_597_){
_start:
{
uint8_t v_isCrossOrigin_boxed_598_; uint8_t v_methodChanged_boxed_599_; lean_object* v_res_600_; 
v_isCrossOrigin_boxed_598_ = lean_unbox(v_isCrossOrigin_596_);
v_methodChanged_boxed_599_ = lean_unbox(v_methodChanged_597_);
v_res_600_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v_headers_595_, v_isCrossOrigin_boxed_598_, v_methodChanged_boxed_599_);
lean_dec_ref(v_headers_595_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg(lean_object* v_map_601_, lean_object* v_key_602_, lean_object* v_x_603_){
_start:
{
lean_object* v_zero_604_; uint8_t v_isZero_605_; 
v_zero_604_ = lean_unsigned_to_nat(0u);
v_isZero_605_ = lean_nat_dec_eq(v_x_603_, v_zero_604_);
if (v_isZero_605_ == 1)
{
lean_object* v___x_606_; 
lean_dec(v_x_603_);
v___x_606_ = lean_array_get_size(v_map_601_);
return v___x_606_;
}
else
{
lean_object* v_one_607_; lean_object* v_n_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v_one_607_ = lean_unsigned_to_nat(1u);
v_n_608_ = lean_nat_sub(v_x_603_, v_one_607_);
lean_dec(v_x_603_);
v___x_609_ = lean_array_get_size(v_map_601_);
v___x_610_ = lean_nat_dec_lt(v_n_608_, v___x_609_);
if (v___x_610_ == 0)
{
lean_dec(v_n_608_);
return v___x_609_;
}
else
{
lean_object* v___x_611_; lean_object* v_fst_612_; uint8_t v___x_613_; 
v___x_611_ = lean_array_fget_borrowed(v_map_601_, v_n_608_);
v_fst_612_ = lean_ctor_get(v___x_611_, 0);
v___x_613_ = lean_string_dec_eq(v_fst_612_, v_key_602_);
if (v___x_613_ == 0)
{
v_x_603_ = v_n_608_;
goto _start;
}
else
{
return v_n_608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg___boxed(lean_object* v_map_615_, lean_object* v_key_616_, lean_object* v_x_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg(v_map_615_, v_key_616_, v_x_617_);
lean_dec_ref(v_key_616_);
lean_dec_ref(v_map_615_);
return v_res_618_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(lean_object* v_as_619_, size_t v_i_620_, size_t v_stop_621_){
_start:
{
uint8_t v___x_622_; 
v___x_622_ = lean_usize_dec_eq(v_i_620_, v_stop_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v_fst_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_623_ = lean_array_uget_borrowed(v_as_619_, v_i_620_);
v_fst_624_ = lean_ctor_get(v___x_623_, 0);
v___x_625_ = l_Std_Http_Header_Name_host;
v___x_626_ = lean_string_dec_eq(v_fst_624_, v___x_625_);
if (v___x_626_ == 0)
{
size_t v___x_627_; size_t v___x_628_; 
v___x_627_ = ((size_t)1ULL);
v___x_628_ = lean_usize_add(v_i_620_, v___x_627_);
v_i_620_ = v___x_628_;
goto _start;
}
else
{
return v___x_626_;
}
}
else
{
uint8_t v___x_630_; 
v___x_630_ = 0;
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0___boxed(lean_object* v_as_631_, lean_object* v_i_632_, lean_object* v_stop_633_){
_start:
{
size_t v_i_boxed_634_; size_t v_stop_boxed_635_; uint8_t v_res_636_; lean_object* v_r_637_; 
v_i_boxed_634_ = lean_unbox_usize(v_i_632_);
lean_dec(v_i_632_);
v_stop_boxed_635_ = lean_unbox_usize(v_stop_633_);
lean_dec(v_stop_633_);
v_res_636_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(v_as_631_, v_i_boxed_634_, v_stop_boxed_635_);
lean_dec_ref(v_as_631_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(lean_object* v_headers_638_, lean_object* v_origin_639_){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_array_get_size(v_headers_638_);
v___x_642_ = lean_nat_dec_lt(v___x_640_, v___x_641_);
if (v___x_642_ == 0)
{
lean_dec_ref(v_origin_639_);
return v_headers_638_;
}
else
{
size_t v___x_643_; size_t v___x_644_; uint8_t v___x_645_; 
v___x_643_ = ((size_t)0ULL);
v___x_644_ = lean_usize_of_nat(v___x_641_);
v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__0(v_headers_638_, v___x_643_, v___x_644_);
if (v___x_645_ == 0)
{
lean_dec_ref(v_origin_639_);
return v_headers_638_;
}
else
{
lean_object* v___x_646_; lean_object* v_i_647_; uint8_t v___x_648_; 
v___x_646_ = l_Std_Http_Header_Name_host;
v_i_647_ = l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg(v_headers_638_, v___x_646_, v___x_641_);
v___x_648_ = lean_nat_dec_lt(v_i_647_, v___x_641_);
if (v___x_648_ == 0)
{
lean_dec(v_i_647_);
lean_dec_ref(v_origin_639_);
return v_headers_638_;
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_649_ = l_Std_Http_URI_Origin_hostHeader(v_origin_639_);
v___x_650_ = l_Std_Http_Header_Value_ofString_x21(v___x_649_);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_646_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_array_fset(v_headers_638_, v_i_647_, v___x_651_);
lean_dec(v_i_647_);
return v___x_652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1(lean_object* v_00_u03b2_653_, lean_object* v_map_654_, lean_object* v_key_655_, lean_object* v_x_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___redArg(v_map_654_, v_key_655_, v_x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1___boxed(lean_object* v_00_u03b2_658_, lean_object* v_map_659_, lean_object* v_key_660_, lean_object* v_x_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Std_Internal_MultiMap_findLastIdxBelow___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader_spec__1(v_00_u03b2_658_, v_map_659_, v_key_660_, v_x_661_);
lean_dec_ref(v_key_660_);
lean_dec_ref(v_map_659_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(lean_object* v_x_663_){
_start:
{
switch(lean_obj_tag(v_x_663_))
{
case 0:
{
lean_object* v_query_664_; 
v_query_664_ = lean_ctor_get(v_x_663_, 1);
lean_inc(v_query_664_);
return v_query_664_;
}
case 1:
{
lean_object* v_uri_665_; lean_object* v_query_666_; 
v_uri_665_ = lean_ctor_get(v_x_663_, 0);
v_query_666_ = lean_ctor_get(v_uri_665_, 3);
lean_inc(v_query_666_);
return v_query_666_;
}
default: 
{
lean_object* v___x_667_; 
v___x_667_ = lean_box(0);
return v___x_667_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f___boxed(lean_object* v_x_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v_x_668_);
lean_dec(v_x_668_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(lean_object* v_ref_670_, uint8_t v_isCrossOrigin_671_, lean_object* v_basePath_672_, lean_object* v_baseQuery_673_, lean_object* v_currentScheme_674_){
_start:
{
lean_object* v___y_676_; lean_object* v___y_677_; 
if (lean_obj_tag(v_ref_670_) == 0)
{
lean_object* v_uri_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_722_; 
lean_dec_ref(v_currentScheme_674_);
lean_dec(v_baseQuery_673_);
lean_dec_ref(v_basePath_672_);
v_uri_680_ = lean_ctor_get(v_ref_670_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v_ref_670_);
if (v_isSharedCheck_722_ == 0)
{
v___x_682_ = v_ref_670_;
v_isShared_683_ = v_isSharedCheck_722_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_uri_680_);
lean_dec(v_ref_670_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_722_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_scheme_684_; lean_object* v_authority_685_; lean_object* v_path_686_; lean_object* v_query_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_720_; 
v_scheme_684_ = lean_ctor_get(v_uri_680_, 0);
v_authority_685_ = lean_ctor_get(v_uri_680_, 1);
v_path_686_ = lean_ctor_get(v_uri_680_, 2);
v_query_687_ = lean_ctor_get(v_uri_680_, 3);
v_isSharedCheck_720_ = !lean_is_exclusive(v_uri_680_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v_uri_680_, 4);
lean_dec(v_unused_721_);
v___x_689_ = v_uri_680_;
v_isShared_690_ = v_isSharedCheck_720_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_query_687_);
lean_inc(v_path_686_);
lean_inc(v_authority_685_);
lean_inc(v_scheme_684_);
lean_dec(v_uri_680_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_720_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___y_692_; 
if (lean_obj_tag(v_authority_685_) == 0)
{
v___y_692_ = v_authority_685_;
goto v___jp_691_;
}
else
{
lean_object* v_val_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_719_; 
v_val_701_ = lean_ctor_get(v_authority_685_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v_authority_685_);
if (v_isSharedCheck_719_ == 0)
{
v___x_703_ = v_authority_685_;
v_isShared_704_ = v_isSharedCheck_719_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_val_701_);
lean_dec(v_authority_685_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_719_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_host_705_; lean_object* v_port_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_717_; 
v_host_705_ = lean_ctor_get(v_val_701_, 1);
v_port_706_ = lean_ctor_get(v_val_701_, 2);
v_isSharedCheck_717_ = !lean_is_exclusive(v_val_701_);
if (v_isSharedCheck_717_ == 0)
{
lean_object* v_unused_718_; 
v_unused_718_ = lean_ctor_get(v_val_701_, 0);
lean_dec(v_unused_718_);
v___x_708_ = v_val_701_;
v_isShared_709_ = v_isSharedCheck_717_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_port_706_);
lean_inc(v_host_705_);
lean_dec(v_val_701_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_717_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_box(0);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_710_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_host_705_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_port_706_);
v___x_712_ = v_reuseFailAlloc_716_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_712_);
v___x_714_ = v___x_703_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
v___y_692_ = v___x_714_;
goto v___jp_691_;
}
}
}
}
}
v___jp_691_:
{
if (v_isCrossOrigin_671_ == 0)
{
lean_object* v___x_693_; 
lean_dec(v___y_692_);
lean_del_object(v___x_689_);
lean_dec_ref(v_scheme_684_);
lean_del_object(v___x_682_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_path_686_);
lean_ctor_set(v___x_693_, 1, v_query_687_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; lean_object* v_stripped_696_; 
v___x_694_ = lean_box(0);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 4, v___x_694_);
lean_ctor_set(v___x_689_, 1, v___y_692_);
v_stripped_696_ = v___x_689_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_scheme_684_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___y_692_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_path_686_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_query_687_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v___x_694_);
v_stripped_696_ = v_reuseFailAlloc_700_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 1);
lean_ctor_set(v___x_682_, 0, v_stripped_696_);
v___x_698_ = v___x_682_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_stripped_696_);
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
}
}
else
{
lean_object* v_ref_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_765_; 
v_ref_723_ = lean_ctor_get(v_ref_670_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v_ref_670_);
if (v_isSharedCheck_765_ == 0)
{
v___x_725_ = v_ref_670_;
v_isShared_726_ = v_isSharedCheck_765_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_ref_723_);
lean_dec(v_ref_670_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_765_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v_authority_727_; 
v_authority_727_ = lean_ctor_get(v_ref_723_, 0);
lean_inc(v_authority_727_);
if (lean_obj_tag(v_authority_727_) == 0)
{
lean_object* v_path_728_; lean_object* v_query_729_; uint8_t v___x_730_; lean_object* v___y_732_; 
lean_del_object(v___x_725_);
lean_dec_ref(v_currentScheme_674_);
v_path_728_ = lean_ctor_get(v_ref_723_, 1);
lean_inc_ref(v_path_728_);
v_query_729_ = lean_ctor_get(v_ref_723_, 2);
lean_inc(v_query_729_);
lean_dec_ref(v_ref_723_);
v___x_730_ = l_Std_Http_URI_Path_isEmpty(v_path_728_);
if (v___x_730_ == 0)
{
uint8_t v_absolute_733_; 
v_absolute_733_ = lean_ctor_get_uint8(v_path_728_, sizeof(void*)*1);
if (v_absolute_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = l_Std_Http_URI_Path_parent(v_basePath_672_);
v___x_735_ = l_Std_Http_URI_Path_join(v___x_734_, v_path_728_);
lean_dec_ref(v_path_728_);
v___y_732_ = v___x_735_;
goto v___jp_731_;
}
else
{
lean_dec_ref(v_basePath_672_);
v___y_732_ = v_path_728_;
goto v___jp_731_;
}
}
else
{
lean_dec_ref(v_path_728_);
v___y_732_ = v_basePath_672_;
goto v___jp_731_;
}
v___jp_731_:
{
if (v___x_730_ == 0)
{
lean_dec(v_baseQuery_673_);
v___y_676_ = v___y_732_;
v___y_677_ = v_query_729_;
goto v___jp_675_;
}
else
{
if (lean_obj_tag(v_query_729_) == 0)
{
v___y_676_ = v___y_732_;
v___y_677_ = v_baseQuery_673_;
goto v___jp_675_;
}
else
{
lean_dec(v_baseQuery_673_);
v___y_676_ = v___y_732_;
v___y_677_ = v_query_729_;
goto v___jp_675_;
}
}
}
}
else
{
lean_dec(v_baseQuery_673_);
lean_dec_ref(v_basePath_672_);
if (v_isCrossOrigin_671_ == 0)
{
lean_object* v_path_736_; lean_object* v_query_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec_ref_known(v_authority_727_, 1);
lean_del_object(v___x_725_);
lean_dec_ref(v_currentScheme_674_);
v_path_736_ = lean_ctor_get(v_ref_723_, 1);
lean_inc_ref(v_path_736_);
v_query_737_ = lean_ctor_get(v_ref_723_, 2);
lean_inc(v_query_737_);
lean_dec_ref(v_ref_723_);
v___x_738_ = l_Std_Http_URI_Path_normalize(v_path_736_);
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v_query_737_);
return v___x_739_;
}
else
{
lean_object* v_val_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_764_; 
v_val_740_ = lean_ctor_get(v_authority_727_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v_authority_727_);
if (v_isSharedCheck_764_ == 0)
{
v___x_742_ = v_authority_727_;
v_isShared_743_ = v_isSharedCheck_764_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_val_740_);
lean_dec(v_authority_727_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_764_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_path_744_; lean_object* v_query_745_; lean_object* v_host_746_; lean_object* v_port_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_762_; 
v_path_744_ = lean_ctor_get(v_ref_723_, 1);
lean_inc_ref(v_path_744_);
v_query_745_ = lean_ctor_get(v_ref_723_, 2);
lean_inc(v_query_745_);
lean_dec_ref(v_ref_723_);
v_host_746_ = lean_ctor_get(v_val_740_, 1);
v_port_747_ = lean_ctor_get(v_val_740_, 2);
v_isSharedCheck_762_ = !lean_is_exclusive(v_val_740_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v_val_740_, 0);
lean_dec(v_unused_763_);
v___x_749_ = v_val_740_;
v_isShared_750_ = v_isSharedCheck_762_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_port_747_);
lean_inc(v_host_746_);
lean_dec(v_val_740_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_762_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v_stripped_753_; 
v___x_751_ = lean_box(0);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_751_);
v_stripped_753_ = v___x_749_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_host_746_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_port_747_);
v_stripped_753_ = v_reuseFailAlloc_761_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v_stripped_753_);
v___x_755_ = v___x_742_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_stripped_753_);
v___x_755_ = v_reuseFailAlloc_760_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v_af_756_; lean_object* v___x_758_; 
v_af_756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_af_756_, 0, v_currentScheme_674_);
lean_ctor_set(v_af_756_, 1, v___x_755_);
lean_ctor_set(v_af_756_, 2, v_path_744_);
lean_ctor_set(v_af_756_, 3, v_query_745_);
lean_ctor_set(v_af_756_, 4, v___x_751_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v_af_756_);
v___x_758_ = v___x_725_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_af_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
}
}
}
}
v___jp_675_:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = l_Std_Http_URI_Path_normalize(v___y_676_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___y_677_);
return v___x_679_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget___boxed(lean_object* v_ref_766_, lean_object* v_isCrossOrigin_767_, lean_object* v_basePath_768_, lean_object* v_baseQuery_769_, lean_object* v_currentScheme_770_){
_start:
{
uint8_t v_isCrossOrigin_boxed_771_; lean_object* v_res_772_; 
v_isCrossOrigin_boxed_771_ = lean_unbox(v_isCrossOrigin_767_);
v_res_772_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v_ref_766_, v_isCrossOrigin_boxed_771_, v_basePath_768_, v_baseQuery_769_, v_currentScheme_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0(lean_object* v___x_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Std_Http_URI_Parser_parseURIReference(v___x_776_, v___y_777_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_pos_779_; lean_object* v_array_780_; lean_object* v_idx_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v_pos_779_ = lean_ctor_get(v___x_778_, 0);
v_array_780_ = lean_ctor_get(v_pos_779_, 0);
v_idx_781_ = lean_ctor_get(v_pos_779_, 1);
v___x_782_ = lean_byte_array_size(v_array_780_);
v___x_783_ = lean_nat_dec_lt(v_idx_781_, v___x_782_);
if (v___x_783_ == 0)
{
return v___x_778_;
}
else
{
lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_791_; 
lean_inc(v_pos_779_);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; lean_object* v_unused_793_; 
v_unused_792_ = lean_ctor_get(v___x_778_, 1);
lean_dec(v_unused_792_);
v_unused_793_ = lean_ctor_get(v___x_778_, 0);
lean_dec(v_unused_793_);
v___x_785_ = v___x_778_;
v_isShared_786_ = v_isSharedCheck_791_;
goto v_resetjp_784_;
}
else
{
lean_dec(v___x_778_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_791_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1));
if (v_isShared_786_ == 0)
{
lean_ctor_set_tag(v___x_785_, 1);
lean_ctor_set(v___x_785_, 1, v___x_787_);
v___x_789_ = v___x_785_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_pos_779_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
return v___x_778_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg(lean_object* v_map_794_, lean_object* v_key_795_, lean_object* v_i_796_){
_start:
{
lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_797_ = lean_array_get_size(v_map_794_);
v___x_798_ = lean_nat_dec_lt(v_i_796_, v___x_797_);
if (v___x_798_ == 0)
{
lean_dec(v_i_796_);
return v___x_797_;
}
else
{
lean_object* v___x_799_; lean_object* v_fst_800_; uint8_t v___x_801_; 
v___x_799_ = lean_array_fget_borrowed(v_map_794_, v_i_796_);
v_fst_800_ = lean_ctor_get(v___x_799_, 0);
v___x_801_ = lean_string_dec_eq(v_fst_800_, v_key_795_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_unsigned_to_nat(1u);
v___x_803_ = lean_nat_add(v_i_796_, v___x_802_);
lean_dec(v_i_796_);
v_i_796_ = v___x_803_;
goto _start;
}
else
{
return v_i_796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg___boxed(lean_object* v_map_805_, lean_object* v_key_806_, lean_object* v_i_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg(v_map_805_, v_key_806_, v_i_807_);
lean_dec_ref(v_key_806_);
lean_dec_ref(v_map_805_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect(lean_object* v_current_821_, lean_object* v_request_822_, uint8_t v_bodyReplayable_823_, uint8_t v_onlySafeRedirects_824_, uint8_t v_responseVersion_825_, lean_object* v_status_826_, lean_object* v_responseHeaders_827_){
_start:
{
lean_object* v___y_829_; lean_object* v___y_830_; uint8_t v___y_831_; uint8_t v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; uint8_t v___y_835_; lean_object* v___y_843_; lean_object* v___y_844_; uint8_t v___y_845_; uint8_t v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_851_; lean_object* v___y_852_; uint8_t v___y_853_; uint8_t v___y_854_; uint8_t v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; uint8_t v___y_858_; lean_object* v___y_864_; lean_object* v___y_865_; uint8_t v___y_866_; uint8_t v___y_867_; uint8_t v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; uint8_t v___y_871_; uint8_t v___y_872_; lean_object* v___y_876_; lean_object* v___y_877_; uint8_t v___y_878_; uint8_t v___y_879_; uint8_t v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; uint8_t v___y_883_; uint8_t v___y_884_; lean_object* v___y_888_; lean_object* v___y_889_; uint8_t v___y_890_; uint8_t v___y_891_; uint8_t v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; uint8_t v___y_895_; uint8_t v___y_896_; lean_object* v___y_899_; lean_object* v___y_900_; uint8_t v___y_901_; uint8_t v___y_902_; uint8_t v___y_903_; lean_object* v___y_904_; uint8_t v___y_905_; uint8_t v___y_906_; lean_object* v___y_907_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; uint8_t v___y_912_; uint8_t v___y_913_; uint8_t v___y_914_; lean_object* v___y_915_; uint8_t v___y_916_; uint8_t v___y_917_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; uint8_t v___y_924_; uint8_t v___y_925_; uint8_t v___y_926_; lean_object* v___y_927_; uint8_t v___y_928_; uint8_t v___y_929_; uint8_t v___y_930_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; uint8_t v___y_937_; uint8_t v___y_938_; uint8_t v___y_939_; lean_object* v___y_940_; uint8_t v___y_941_; uint8_t v___y_942_; uint8_t v___y_943_; uint8_t v___y_944_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; uint8_t v___y_949_; uint8_t v___y_950_; uint8_t v___y_951_; lean_object* v___y_952_; uint8_t v___y_953_; uint8_t v___y_954_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; uint8_t v___y_961_; uint8_t v___y_962_; uint8_t v___y_963_; lean_object* v___y_964_; uint8_t v___y_965_; uint8_t v___y_966_; uint8_t v___y_967_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; uint8_t v___y_972_; uint8_t v___y_973_; uint8_t v___y_974_; lean_object* v___y_975_; uint8_t v___y_976_; uint8_t v___y_977_; uint8_t v___y_978_; uint8_t v___y_979_; uint16_t v___x_982_; uint16_t v___x_983_; uint8_t v___x_984_; 
v___x_982_ = 300;
v___x_983_ = l_Std_Http_Status_toCode(v_status_826_);
v___x_984_ = lean_uint16_dec_le(v___x_982_, v___x_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
lean_dec_ref(v_current_821_);
v___x_985_ = lean_box(0);
return v___x_985_;
}
else
{
uint16_t v___x_986_; uint8_t v___x_987_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; uint8_t v___y_992_; uint8_t v___y_993_; lean_object* v___y_994_; uint8_t v___y_995_; uint8_t v___y_996_; uint8_t v___y_997_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; uint8_t v___y_1006_; lean_object* v___y_1007_; uint8_t v___y_1008_; uint8_t v___y_1009_; uint8_t v___y_1010_; uint8_t v___y_1011_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; uint8_t v___y_1017_; lean_object* v___y_1018_; uint8_t v___y_1019_; uint8_t v___y_1020_; uint8_t v___y_1021_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v_scheme_1027_; uint8_t v___y_1028_; lean_object* v___y_1029_; uint8_t v___y_1030_; uint8_t v___y_1031_; uint8_t v___y_1032_; 
v___x_986_ = 400;
v___x_987_ = lean_uint16_dec_lt(v___x_983_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_1037_; 
lean_dec_ref(v_current_821_);
v___x_1037_ = lean_box(0);
return v___x_1037_;
}
else
{
uint8_t v___x_1038_; uint8_t v___y_1040_; uint8_t v___x_1080_; uint8_t v___x_1081_; 
v___x_1038_ = 0;
v___x_1080_ = 0;
v___x_1081_ = l_Std_Http_instBEqVersion_beq(v_responseVersion_825_, v___x_1080_);
if (v___x_1081_ == 0)
{
goto v___jp_1064_;
}
else
{
lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = lean_box(15);
v___x_1083_ = l_Std_Http_instBEqStatus_beq(v_status_826_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = lean_box(16);
v___x_1085_ = l_Std_Http_instBEqStatus_beq(v_status_826_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
lean_dec_ref(v_current_821_);
v___x_1086_ = lean_box(0);
return v___x_1086_;
}
else
{
goto v___jp_1064_;
}
}
else
{
goto v___jp_1064_;
}
}
v___jp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v_i_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1041_ = l_Std_Http_Header_Name_location;
v___x_1042_ = lean_unsigned_to_nat(0u);
v_i_1043_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg(v_responseHeaders_827_, v___x_1041_, v___x_1042_);
v___x_1044_ = lean_array_get_size(v_responseHeaders_827_);
v___x_1045_ = lean_nat_dec_lt(v_i_1043_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; 
lean_dec(v_i_1043_);
lean_dec_ref(v_current_821_);
v___x_1046_ = lean_box(0);
return v___x_1046_;
}
else
{
lean_object* v___x_1047_; lean_object* v_snd_1048_; lean_object* v___f_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1047_ = lean_array_fget_borrowed(v_responseHeaders_827_, v_i_1043_);
lean_dec(v_i_1043_);
v_snd_1048_ = lean_ctor_get(v___x_1047_, 1);
v___f_1049_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__2));
lean_inc(v_snd_1048_);
v___x_1050_ = lean_string_to_utf8(v_snd_1048_);
v___x_1051_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1049_, v___x_1050_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v___x_1052_; 
lean_dec_ref_known(v___x_1051_, 1);
lean_dec_ref(v_current_821_);
v___x_1052_ = lean_box(0);
return v___x_1052_;
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1054_; 
v_a_1053_ = lean_ctor_get(v___x_1051_, 0);
lean_inc_n(v_a_1053_, 2);
lean_dec_ref_known(v___x_1051_, 1);
lean_inc_ref(v_current_821_);
v___x_1054_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(v_current_821_, v_a_1053_);
if (lean_obj_tag(v___x_1054_) == 1)
{
lean_object* v_val_1055_; uint8_t v_method_1056_; lean_object* v_uri_1057_; lean_object* v_headers_1058_; lean_object* v_scheme_1059_; uint8_t v_newMethod_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v_val_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_val_1055_);
lean_dec_ref_known(v___x_1054_, 1);
v_method_1056_ = lean_ctor_get_uint8(v_request_822_, sizeof(void*)*2);
v_uri_1057_ = lean_ctor_get(v_request_822_, 0);
v_headers_1058_ = lean_ctor_get(v_request_822_, 1);
v_scheme_1059_ = lean_ctor_get(v_val_1055_, 0);
v_newMethod_1060_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_method_1056_, v_responseVersion_825_, v_status_826_);
v___x_1061_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__3));
v___x_1062_ = lean_string_dec_eq(v_scheme_1059_, v___x_1061_);
if (v___x_1062_ == 0)
{
lean_inc_ref(v_scheme_1059_);
v___y_1024_ = v_uri_1057_;
v___y_1025_ = v_headers_1058_;
v___y_1026_ = v_val_1055_;
v_scheme_1027_ = v_scheme_1059_;
v___y_1028_ = v_newMethod_1060_;
v___y_1029_ = v_a_1053_;
v___y_1030_ = v_method_1056_;
v___y_1031_ = v___x_1045_;
v___y_1032_ = v___y_1040_;
goto v___jp_1023_;
}
else
{
if (v___y_1040_ == 0)
{
v___y_1014_ = v_headers_1058_;
v___y_1015_ = v_val_1055_;
v___y_1016_ = v_uri_1057_;
v___y_1017_ = v_newMethod_1060_;
v___y_1018_ = v_a_1053_;
v___y_1019_ = v_method_1056_;
v___y_1020_ = v___x_1045_;
v___y_1021_ = v___x_1038_;
goto v___jp_1013_;
}
else
{
lean_inc_ref(v_scheme_1059_);
v___y_1024_ = v_uri_1057_;
v___y_1025_ = v_headers_1058_;
v___y_1026_ = v_val_1055_;
v_scheme_1027_ = v_scheme_1059_;
v___y_1028_ = v_newMethod_1060_;
v___y_1029_ = v_a_1053_;
v___y_1030_ = v_method_1056_;
v___y_1031_ = v___x_1045_;
v___y_1032_ = v___y_1040_;
goto v___jp_1023_;
}
}
}
else
{
lean_object* v___x_1063_; 
lean_dec(v___x_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_current_821_);
v___x_1063_ = lean_box(0);
return v___x_1063_;
}
}
}
}
v___jp_1064_:
{
lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = lean_box(19);
v___x_1066_ = l_Std_Http_instBEqStatus_beq(v_status_826_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = lean_box(20);
v___x_1068_ = l_Std_Http_instBEqStatus_beq(v_status_826_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = lean_box(18);
v___x_1070_ = l_Std_Http_instBEqStatus_beq(v_status_826_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = lean_box(14);
v___x_1072_ = l_Std_Http_instBEqStatus_beq(v_status_826_, v___x_1071_);
if (v___x_1072_ == 0)
{
if (v_onlySafeRedirects_824_ == 0)
{
v___y_1040_ = v___x_1038_;
goto v___jp_1039_;
}
else
{
uint8_t v_method_1073_; uint8_t v___x_1074_; 
v_method_1073_ = lean_ctor_get_uint8(v_request_822_, sizeof(void*)*2);
v___x_1074_ = l_Std_Http_Method_isSafe(v_method_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; 
lean_dec_ref(v_current_821_);
v___x_1075_ = lean_box(0);
return v___x_1075_;
}
else
{
v___y_1040_ = v___x_1072_;
goto v___jp_1039_;
}
}
}
else
{
lean_object* v___x_1076_; 
lean_dec_ref(v_current_821_);
v___x_1076_ = lean_box(0);
return v___x_1076_;
}
}
else
{
lean_object* v___x_1077_; 
lean_dec_ref(v_current_821_);
v___x_1077_ = lean_box(0);
return v___x_1077_;
}
}
else
{
lean_object* v___x_1078_; 
lean_dec_ref(v_current_821_);
v___x_1078_ = lean_box(0);
return v___x_1078_;
}
}
else
{
lean_object* v___x_1079_; 
lean_dec_ref(v_current_821_);
v___x_1079_ = lean_box(0);
return v___x_1079_;
}
}
}
v___jp_988_:
{
uint8_t v___x_998_; uint8_t v___x_999_; 
v___x_998_ = 8;
v___x_999_ = l_Std_Http_instBEqMethod_beq(v___y_995_, v___x_998_);
if (v___x_999_ == 0)
{
uint8_t v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = 9;
v___x_1001_ = l_Std_Http_instBEqMethod_beq(v___y_995_, v___x_1000_);
v___y_969_ = v___y_989_;
v___y_970_ = v___y_991_;
v___y_971_ = v___y_990_;
v___y_972_ = v___y_992_;
v___y_973_ = v___y_993_;
v___y_974_ = v___x_998_;
v___y_975_ = v___y_994_;
v___y_976_ = v___y_995_;
v___y_977_ = v___y_997_;
v___y_978_ = v___y_996_;
v___y_979_ = v___x_1001_;
goto v___jp_968_;
}
else
{
v___y_969_ = v___y_989_;
v___y_970_ = v___y_991_;
v___y_971_ = v___y_990_;
v___y_972_ = v___y_992_;
v___y_973_ = v___y_993_;
v___y_974_ = v___x_998_;
v___y_975_ = v___y_994_;
v___y_976_ = v___y_995_;
v___y_977_ = v___y_997_;
v___y_978_ = v___y_996_;
v___y_979_ = v___x_987_;
goto v___jp_968_;
}
}
v___jp_1002_:
{
uint8_t v___x_1012_; 
v___x_1012_ = l_Std_Http_instBEqMethod_beq(v___y_1006_, v___y_1008_);
if (v___x_1012_ == 0)
{
v___y_989_ = v___y_1005_;
v___y_990_ = v___y_1004_;
v___y_991_ = v___y_1003_;
v___y_992_ = v___y_1006_;
v___y_993_ = v___y_1011_;
v___y_994_ = v___y_1007_;
v___y_995_ = v___y_1008_;
v___y_996_ = v___y_1010_;
v___y_997_ = v___y_1009_;
goto v___jp_988_;
}
else
{
v___y_989_ = v___y_1005_;
v___y_990_ = v___y_1004_;
v___y_991_ = v___y_1003_;
v___y_992_ = v___y_1006_;
v___y_993_ = v___y_1011_;
v___y_994_ = v___y_1007_;
v___y_995_ = v___y_1008_;
v___y_996_ = v___y_1010_;
v___y_997_ = v___y_1010_;
goto v___jp_988_;
}
}
v___jp_1013_:
{
uint8_t v___x_1022_; 
v___x_1022_ = l_Std_Http_URI_instBEqOrigin_beq(v___y_1015_, v_current_821_);
if (v___x_1022_ == 0)
{
v___y_1003_ = v___y_1016_;
v___y_1004_ = v___y_1015_;
v___y_1005_ = v___y_1014_;
v___y_1006_ = v___y_1017_;
v___y_1007_ = v___y_1018_;
v___y_1008_ = v___y_1019_;
v___y_1009_ = v___y_1020_;
v___y_1010_ = v___y_1021_;
v___y_1011_ = v___y_1020_;
goto v___jp_1002_;
}
else
{
v___y_1003_ = v___y_1016_;
v___y_1004_ = v___y_1015_;
v___y_1005_ = v___y_1014_;
v___y_1006_ = v___y_1017_;
v___y_1007_ = v___y_1018_;
v___y_1008_ = v___y_1019_;
v___y_1009_ = v___y_1020_;
v___y_1010_ = v___y_1021_;
v___y_1011_ = v___y_1021_;
goto v___jp_1002_;
}
}
v___jp_1023_:
{
lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1033_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__0));
v___x_1034_ = lean_string_dec_eq(v_scheme_1027_, v___x_1033_);
lean_dec_ref(v_scheme_1027_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; 
lean_dec_ref(v___y_1029_);
lean_dec_ref(v___y_1026_);
lean_dec_ref(v_current_821_);
v___x_1035_ = lean_box(0);
return v___x_1035_;
}
else
{
if (v___y_1032_ == 0)
{
v___y_1014_ = v___y_1025_;
v___y_1015_ = v___y_1026_;
v___y_1016_ = v___y_1024_;
v___y_1017_ = v___y_1028_;
v___y_1018_ = v___y_1029_;
v___y_1019_ = v___y_1030_;
v___y_1020_ = v___y_1031_;
v___y_1021_ = v___y_1032_;
goto v___jp_1013_;
}
else
{
lean_object* v___x_1036_; 
lean_dec_ref(v___y_1029_);
lean_dec_ref(v___y_1026_);
lean_dec_ref(v_current_821_);
v___x_1036_ = lean_box(0);
return v___x_1036_;
}
}
}
}
v___jp_828_:
{
lean_object* v_scheme_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v_rewrittenTarget_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_scheme_836_ = lean_ctor_get(v_current_821_, 0);
lean_inc_ref(v_scheme_836_);
lean_dec_ref(v_current_821_);
v___x_837_ = l_Std_Http_RequestTarget_pathOrRoot(v___y_830_);
v___x_838_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v___y_830_);
v_rewrittenTarget_839_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v___y_834_, v___y_832_, v___x_837_, v___x_838_, v_scheme_836_);
v___x_840_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_840_, 0, v___y_829_);
lean_ctor_set(v___x_840_, 1, v_rewrittenTarget_839_);
lean_ctor_set(v___x_840_, 2, v___y_833_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3, v___y_831_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 1, v___y_835_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 2, v___y_832_);
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
v___jp_842_:
{
uint8_t v___x_849_; 
v___x_849_ = 0;
v___y_829_ = v___y_844_;
v___y_830_ = v___y_843_;
v___y_831_ = v___y_845_;
v___y_832_ = v___y_846_;
v___y_833_ = v___y_847_;
v___y_834_ = v___y_848_;
v___y_835_ = v___x_849_;
goto v___jp_828_;
}
v___jp_850_:
{
uint8_t v___x_859_; 
v___x_859_ = l_Std_Http_instBEqMethod_beq(v___y_853_, v___y_855_);
if (v___x_859_ == 0)
{
uint8_t v___x_860_; uint8_t v___x_861_; 
v___x_860_ = 9;
v___x_861_ = l_Std_Http_instBEqMethod_beq(v___y_853_, v___x_860_);
if (v___x_861_ == 0)
{
if (v___y_858_ == 0)
{
uint8_t v___x_862_; 
v___x_862_ = 1;
v___y_829_ = v___y_852_;
v___y_830_ = v___y_851_;
v___y_831_ = v___y_853_;
v___y_832_ = v___y_854_;
v___y_833_ = v___y_856_;
v___y_834_ = v___y_857_;
v___y_835_ = v___x_862_;
goto v___jp_828_;
}
else
{
v___y_843_ = v___y_851_;
v___y_844_ = v___y_852_;
v___y_845_ = v___y_853_;
v___y_846_ = v___y_854_;
v___y_847_ = v___y_856_;
v___y_848_ = v___y_857_;
goto v___jp_842_;
}
}
else
{
v___y_843_ = v___y_851_;
v___y_844_ = v___y_852_;
v___y_845_ = v___y_853_;
v___y_846_ = v___y_854_;
v___y_847_ = v___y_856_;
v___y_848_ = v___y_857_;
goto v___jp_842_;
}
}
else
{
v___y_843_ = v___y_851_;
v___y_844_ = v___y_852_;
v___y_845_ = v___y_853_;
v___y_846_ = v___y_854_;
v___y_847_ = v___y_856_;
v___y_848_ = v___y_857_;
goto v___jp_842_;
}
}
v___jp_863_:
{
if (v_bodyReplayable_823_ == 0)
{
lean_object* v___x_873_; 
lean_dec_ref(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec_ref(v___y_864_);
lean_dec_ref(v_current_821_);
v___x_873_ = lean_box(0);
return v___x_873_;
}
else
{
if (v___y_872_ == 0)
{
v___y_851_ = v___y_865_;
v___y_852_ = v___y_864_;
v___y_853_ = v___y_866_;
v___y_854_ = v___y_868_;
v___y_855_ = v___y_867_;
v___y_856_ = v___y_869_;
v___y_857_ = v___y_870_;
v___y_858_ = v___y_871_;
goto v___jp_850_;
}
else
{
lean_object* v___x_874_; 
lean_dec_ref(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec_ref(v___y_864_);
lean_dec_ref(v_current_821_);
v___x_874_ = lean_box(0);
return v___x_874_;
}
}
}
v___jp_875_:
{
uint8_t v___x_885_; uint8_t v___x_886_; 
v___x_885_ = 9;
v___x_886_ = l_Std_Http_instBEqMethod_beq(v___y_878_, v___x_885_);
if (v___x_886_ == 0)
{
v___y_864_ = v___y_877_;
v___y_865_ = v___y_876_;
v___y_866_ = v___y_878_;
v___y_867_ = v___y_880_;
v___y_868_ = v___y_879_;
v___y_869_ = v___y_881_;
v___y_870_ = v___y_882_;
v___y_871_ = v___y_883_;
v___y_872_ = v___y_884_;
goto v___jp_863_;
}
else
{
if (v___y_884_ == 0)
{
v___y_851_ = v___y_876_;
v___y_852_ = v___y_877_;
v___y_853_ = v___y_878_;
v___y_854_ = v___y_879_;
v___y_855_ = v___y_880_;
v___y_856_ = v___y_881_;
v___y_857_ = v___y_882_;
v___y_858_ = v___y_883_;
goto v___jp_850_;
}
else
{
v___y_864_ = v___y_877_;
v___y_865_ = v___y_876_;
v___y_866_ = v___y_878_;
v___y_867_ = v___y_880_;
v___y_868_ = v___y_879_;
v___y_869_ = v___y_881_;
v___y_870_ = v___y_882_;
v___y_871_ = v___y_883_;
v___y_872_ = v___y_884_;
goto v___jp_863_;
}
}
}
v___jp_887_:
{
uint8_t v___x_897_; 
v___x_897_ = l_Std_Http_instBEqMethod_beq(v___y_890_, v___y_892_);
if (v___x_897_ == 0)
{
v___y_876_ = v___y_889_;
v___y_877_ = v___y_888_;
v___y_878_ = v___y_890_;
v___y_879_ = v___y_891_;
v___y_880_ = v___y_892_;
v___y_881_ = v___y_893_;
v___y_882_ = v___y_894_;
v___y_883_ = v___y_895_;
v___y_884_ = v___y_896_;
goto v___jp_875_;
}
else
{
if (v___y_896_ == 0)
{
v___y_851_ = v___y_889_;
v___y_852_ = v___y_888_;
v___y_853_ = v___y_890_;
v___y_854_ = v___y_891_;
v___y_855_ = v___y_892_;
v___y_856_ = v___y_893_;
v___y_857_ = v___y_894_;
v___y_858_ = v___y_895_;
goto v___jp_850_;
}
else
{
v___y_876_ = v___y_889_;
v___y_877_ = v___y_888_;
v___y_878_ = v___y_890_;
v___y_879_ = v___y_891_;
v___y_880_ = v___y_892_;
v___y_881_ = v___y_893_;
v___y_882_ = v___y_894_;
v___y_883_ = v___y_895_;
v___y_884_ = v___y_896_;
goto v___jp_875_;
}
}
}
v___jp_898_:
{
if (v___y_905_ == 0)
{
v___y_888_ = v___y_900_;
v___y_889_ = v___y_899_;
v___y_890_ = v___y_901_;
v___y_891_ = v___y_903_;
v___y_892_ = v___y_902_;
v___y_893_ = v___y_907_;
v___y_894_ = v___y_904_;
v___y_895_ = v___y_905_;
v___y_896_ = v___y_906_;
goto v___jp_887_;
}
else
{
if (v___y_906_ == 0)
{
v___y_851_ = v___y_899_;
v___y_852_ = v___y_900_;
v___y_853_ = v___y_901_;
v___y_854_ = v___y_903_;
v___y_855_ = v___y_902_;
v___y_856_ = v___y_907_;
v___y_857_ = v___y_904_;
v___y_858_ = v___y_905_;
goto v___jp_850_;
}
else
{
v___y_888_ = v___y_900_;
v___y_889_ = v___y_899_;
v___y_890_ = v___y_901_;
v___y_891_ = v___y_903_;
v___y_892_ = v___y_902_;
v___y_893_ = v___y_907_;
v___y_894_ = v___y_904_;
v___y_895_ = v___y_905_;
v___y_896_ = v___y_906_;
goto v___jp_887_;
}
}
}
v___jp_908_:
{
lean_object* v_scrubbed_918_; 
v_scrubbed_918_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v___y_911_, v___y_914_, v___y_916_);
if (v___y_914_ == 0)
{
v___y_899_ = v___y_910_;
v___y_900_ = v___y_909_;
v___y_901_ = v___y_912_;
v___y_902_ = v___y_913_;
v___y_903_ = v___y_914_;
v___y_904_ = v___y_915_;
v___y_905_ = v___y_916_;
v___y_906_ = v___y_917_;
v___y_907_ = v_scrubbed_918_;
goto v___jp_898_;
}
else
{
lean_object* v___x_919_; 
lean_inc_ref(v___y_909_);
v___x_919_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(v_scrubbed_918_, v___y_909_);
v___y_899_ = v___y_910_;
v___y_900_ = v___y_909_;
v___y_901_ = v___y_912_;
v___y_902_ = v___y_913_;
v___y_903_ = v___y_914_;
v___y_904_ = v___y_915_;
v___y_905_ = v___y_916_;
v___y_906_ = v___y_917_;
v___y_907_ = v___x_919_;
goto v___jp_898_;
}
}
v___jp_920_:
{
if (v___y_929_ == 0)
{
lean_object* v___x_931_; 
lean_dec_ref(v___y_927_);
lean_dec_ref(v___y_923_);
lean_dec_ref(v_current_821_);
v___x_931_ = lean_box(0);
return v___x_931_;
}
else
{
if (v___y_930_ == 0)
{
v___y_909_ = v___y_923_;
v___y_910_ = v___y_922_;
v___y_911_ = v___y_921_;
v___y_912_ = v___y_924_;
v___y_913_ = v___y_926_;
v___y_914_ = v___y_925_;
v___y_915_ = v___y_927_;
v___y_916_ = v___y_928_;
v___y_917_ = v___y_930_;
goto v___jp_908_;
}
else
{
lean_object* v___x_932_; 
lean_dec_ref(v___y_927_);
lean_dec_ref(v___y_923_);
lean_dec_ref(v_current_821_);
v___x_932_ = lean_box(0);
return v___x_932_;
}
}
}
v___jp_933_:
{
if (v___y_943_ == 0)
{
v___y_921_ = v___y_936_;
v___y_922_ = v___y_935_;
v___y_923_ = v___y_934_;
v___y_924_ = v___y_937_;
v___y_925_ = v___y_939_;
v___y_926_ = v___y_938_;
v___y_927_ = v___y_940_;
v___y_928_ = v___y_941_;
v___y_929_ = v___y_942_;
v___y_930_ = v___y_944_;
goto v___jp_920_;
}
else
{
if (v___y_944_ == 0)
{
v___y_909_ = v___y_934_;
v___y_910_ = v___y_935_;
v___y_911_ = v___y_936_;
v___y_912_ = v___y_937_;
v___y_913_ = v___y_938_;
v___y_914_ = v___y_939_;
v___y_915_ = v___y_940_;
v___y_916_ = v___y_941_;
v___y_917_ = v___y_944_;
goto v___jp_908_;
}
else
{
v___y_921_ = v___y_936_;
v___y_922_ = v___y_935_;
v___y_923_ = v___y_934_;
v___y_924_ = v___y_937_;
v___y_925_ = v___y_939_;
v___y_926_ = v___y_938_;
v___y_927_ = v___y_940_;
v___y_928_ = v___y_941_;
v___y_929_ = v___y_942_;
v___y_930_ = v___y_944_;
goto v___jp_920_;
}
}
}
v___jp_945_:
{
if (v_bodyReplayable_823_ == 0)
{
lean_object* v___x_955_; 
lean_dec_ref(v___y_952_);
lean_dec_ref(v___y_948_);
lean_dec_ref(v_current_821_);
v___x_955_ = lean_box(0);
return v___x_955_;
}
else
{
if (v___y_954_ == 0)
{
v___y_909_ = v___y_948_;
v___y_910_ = v___y_947_;
v___y_911_ = v___y_946_;
v___y_912_ = v___y_949_;
v___y_913_ = v___y_951_;
v___y_914_ = v___y_950_;
v___y_915_ = v___y_952_;
v___y_916_ = v___y_953_;
v___y_917_ = v___y_954_;
goto v___jp_908_;
}
else
{
lean_object* v___x_956_; 
lean_dec_ref(v___y_952_);
lean_dec_ref(v___y_948_);
lean_dec_ref(v_current_821_);
v___x_956_ = lean_box(0);
return v___x_956_;
}
}
}
v___jp_957_:
{
if (v___y_966_ == 0)
{
v___y_946_ = v___y_960_;
v___y_947_ = v___y_959_;
v___y_948_ = v___y_958_;
v___y_949_ = v___y_961_;
v___y_950_ = v___y_963_;
v___y_951_ = v___y_962_;
v___y_952_ = v___y_964_;
v___y_953_ = v___y_965_;
v___y_954_ = v___y_967_;
goto v___jp_945_;
}
else
{
if (v___y_967_ == 0)
{
v___y_909_ = v___y_958_;
v___y_910_ = v___y_959_;
v___y_911_ = v___y_960_;
v___y_912_ = v___y_961_;
v___y_913_ = v___y_962_;
v___y_914_ = v___y_963_;
v___y_915_ = v___y_964_;
v___y_916_ = v___y_965_;
v___y_917_ = v___y_967_;
goto v___jp_908_;
}
else
{
v___y_946_ = v___y_960_;
v___y_947_ = v___y_959_;
v___y_948_ = v___y_958_;
v___y_949_ = v___y_961_;
v___y_950_ = v___y_963_;
v___y_951_ = v___y_962_;
v___y_952_ = v___y_964_;
v___y_953_ = v___y_965_;
v___y_954_ = v___y_967_;
goto v___jp_945_;
}
}
}
v___jp_968_:
{
uint8_t v___x_980_; uint8_t v_isPost_981_; 
v___x_980_ = 23;
v_isPost_981_ = l_Std_Http_instBEqMethod_beq(v___y_976_, v___x_980_);
switch(lean_obj_tag(v_status_826_))
{
case 15:
{
v___y_934_ = v___y_971_;
v___y_935_ = v___y_970_;
v___y_936_ = v___y_969_;
v___y_937_ = v___y_972_;
v___y_938_ = v___y_974_;
v___y_939_ = v___y_973_;
v___y_940_ = v___y_975_;
v___y_941_ = v___y_977_;
v___y_942_ = v_isPost_981_;
v___y_943_ = v___y_979_;
v___y_944_ = v___y_978_;
goto v___jp_933_;
}
case 16:
{
v___y_934_ = v___y_971_;
v___y_935_ = v___y_970_;
v___y_936_ = v___y_969_;
v___y_937_ = v___y_972_;
v___y_938_ = v___y_974_;
v___y_939_ = v___y_973_;
v___y_940_ = v___y_975_;
v___y_941_ = v___y_977_;
v___y_942_ = v_isPost_981_;
v___y_943_ = v___y_979_;
v___y_944_ = v___y_978_;
goto v___jp_933_;
}
case 21:
{
v___y_958_ = v___y_971_;
v___y_959_ = v___y_970_;
v___y_960_ = v___y_969_;
v___y_961_ = v___y_972_;
v___y_962_ = v___y_974_;
v___y_963_ = v___y_973_;
v___y_964_ = v___y_975_;
v___y_965_ = v___y_977_;
v___y_966_ = v___y_979_;
v___y_967_ = v___y_978_;
goto v___jp_957_;
}
case 22:
{
v___y_958_ = v___y_971_;
v___y_959_ = v___y_970_;
v___y_960_ = v___y_969_;
v___y_961_ = v___y_972_;
v___y_962_ = v___y_974_;
v___y_963_ = v___y_973_;
v___y_964_ = v___y_975_;
v___y_965_ = v___y_977_;
v___y_966_ = v___y_979_;
v___y_967_ = v___y_978_;
goto v___jp_957_;
}
default: 
{
v___y_909_ = v___y_971_;
v___y_910_ = v___y_970_;
v___y_911_ = v___y_969_;
v___y_912_ = v___y_972_;
v___y_913_ = v___y_974_;
v___y_914_ = v___y_973_;
v___y_915_ = v___y_975_;
v___y_916_ = v___y_977_;
v___y_917_ = v___y_978_;
goto v___jp_908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___boxed(lean_object* v_current_1087_, lean_object* v_request_1088_, lean_object* v_bodyReplayable_1089_, lean_object* v_onlySafeRedirects_1090_, lean_object* v_responseVersion_1091_, lean_object* v_status_1092_, lean_object* v_responseHeaders_1093_){
_start:
{
uint8_t v_bodyReplayable_boxed_1094_; uint8_t v_onlySafeRedirects_boxed_1095_; uint8_t v_responseVersion_boxed_1096_; lean_object* v_res_1097_; 
v_bodyReplayable_boxed_1094_ = lean_unbox(v_bodyReplayable_1089_);
v_onlySafeRedirects_boxed_1095_ = lean_unbox(v_onlySafeRedirects_1090_);
v_responseVersion_boxed_1096_ = lean_unbox(v_responseVersion_1091_);
v_res_1097_ = l_Std_Http_Protocol_H1_decideRedirect(v_current_1087_, v_request_1088_, v_bodyReplayable_boxed_1094_, v_onlySafeRedirects_boxed_1095_, v_responseVersion_boxed_1096_, v_status_1092_, v_responseHeaders_1093_);
lean_dec_ref(v_responseHeaders_1093_);
lean_dec(v_status_1092_);
lean_dec_ref(v_request_1088_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0(lean_object* v_00_u03b2_1098_, lean_object* v_map_1099_, lean_object* v_key_1100_, lean_object* v_i_1101_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___redArg(v_map_1099_, v_key_1100_, v_i_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0___boxed(lean_object* v_00_u03b2_1103_, lean_object* v_map_1104_, lean_object* v_key_1105_, lean_object* v_i_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Std_Internal_MultiMap_findIdxFrom___at___00Std_Http_Protocol_H1_decideRedirect_spec__0(v_00_u03b2_1103_, v_map_1104_, v_key_1105_, v_i_1106_);
lean_dec_ref(v_key_1105_);
lean_dec_ref(v_map_1104_);
return v_res_1107_;
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
