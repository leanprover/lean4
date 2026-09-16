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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_Http_Header_Name_ofString_x3f(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_host;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_Origin_hostHeader(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_proxyAuthorization;
extern lean_object* l_Std_Http_Header_Name_lastModified;
extern lean_object* l_Std_Http_Header_Name_contentLocation;
extern lean_object* l_Std_Http_Header_Name_contentLanguage;
extern lean_object* l_Std_Http_Header_Name_contentEncoding;
extern lean_object* l_Std_Http_Header_Name_contentLength;
extern lean_object* l_Std_Http_Header_Name_contentType;
uint16_t l_Std_Http_URI_Scheme_defaultPort(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_connection;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
uint8_t l_Std_Http_URI_instBEqOrigin_beq(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_location;
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
uint8_t l_Std_Http_instBEqVersion_beq(uint8_t, uint8_t);
uint8_t l_Std_Http_instBEqStatus_beq(lean_object*, lean_object*);
uint8_t l_Std_Http_Method_isSafe(uint8_t);
uint16_t l_Std_Http_Status_toCode(lean_object*);
uint8_t lean_uint16_dec_le(uint16_t, uint16_t);
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0 = (const lean_object*)&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__0 = (const lean_object*)&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx(uint8_t v_x_1_){
_start:
{
if (v_x_1_ == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx(v_x_boxed_5_);
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
lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_58_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx(v_x_56_);
v___x_59_ = l_Std_Http_Protocol_H1_RedirectBodyAction_ctorIdx(v_y_57_);
v___x_60_ = lean_nat_dec_eq(v___x_58_, v___x_59_);
lean_dec(v___x_59_);
lean_dec(v___x_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction___boxed(lean_object* v_x_61_, lean_object* v_y_62_){
_start:
{
uint8_t v_x_20__boxed_63_; uint8_t v_y_21__boxed_64_; uint8_t v_res_65_; lean_object* v_r_66_; 
v_x_20__boxed_63_ = lean_unbox(v_x_61_);
v_y_21__boxed_64_ = lean_unbox(v_y_62_);
v_res_65_ = l_Std_Http_Protocol_H1_instDecidableEqRedirectBodyAction(v_x_20__boxed_63_, v_y_21__boxed_64_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(2u);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_to_int(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(uint8_t v_x_77_, lean_object* v_prec_78_){
_start:
{
lean_object* v___y_80_; lean_object* v___y_87_; 
if (v_x_77_ == 0)
{
lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = lean_unsigned_to_nat(1024u);
v___x_94_ = lean_nat_dec_le(v___x_93_, v_prec_78_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; 
v___x_95_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4);
v___y_80_ = v___x_95_;
goto v___jp_79_;
}
else
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5);
v___y_80_ = v___x_96_;
goto v___jp_79_;
}
}
else
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(1024u);
v___x_98_ = lean_nat_dec_le(v___x_97_, v_prec_78_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__4);
v___y_87_ = v___x_99_;
goto v___jp_86_;
}
else
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5, &l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5_once, _init_l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__5);
v___y_87_ = v___x_100_;
goto v___jp_86_;
}
}
v___jp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_81_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__1));
lean_inc(v___y_80_);
v___x_82_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_82_, 0, v___y_80_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = 0;
v___x_84_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___x_83_);
v___x_85_ = l_Repr_addAppParen(v___x_84_, v_prec_78_);
return v___x_85_;
}
v___jp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_88_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___closed__3));
lean_inc(v___y_87_);
v___x_89_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_89_, 0, v___y_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = 0;
v___x_91_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*1, v___x_90_);
v___x_92_ = l_Repr_addAppParen(v___x_91_, v_prec_78_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr___boxed(lean_object* v_x_101_, lean_object* v_prec_102_){
_start:
{
uint8_t v_x_117__boxed_103_; lean_object* v_res_104_; 
v_x_117__boxed_103_ = lean_unbox(v_x_101_);
v_res_104_ = l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(v_x_117__boxed_103_, v_prec_102_);
lean_dec(v_prec_102_);
return v_res_104_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction_default(void){
_start:
{
uint8_t v___x_107_; 
v___x_107_ = 0;
return v___x_107_;
}
}
static uint8_t _init_l_Std_Http_Protocol_H1_instInhabitedRedirectBodyAction(void){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = 0;
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Protocol_H1_instReprRedirectPlan_repr_spec__0(lean_object* v_a_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_nat_to_int(v_a_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(10u);
v___x_125_ = lean_nat_to_int(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(11u);
v___x_139_ = lean_nat_to_int(v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_unsigned_to_nat(14u);
v___x_144_ = lean_nat_to_int(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(17u);
v___x_149_ = lean_nat_to_int(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__0));
v___x_152_ = lean_string_length(v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__24);
v___x_154_ = lean_nat_to_int(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg(lean_object* v_x_159_){
_start:
{
lean_object* v_origin_160_; lean_object* v_target_161_; uint8_t v_method_162_; lean_object* v_headers_163_; uint8_t v_bodyAction_164_; uint8_t v_isCrossOrigin_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_origin_160_ = lean_ctor_get(v_x_159_, 0);
lean_inc_ref(v_origin_160_);
v_target_161_ = lean_ctor_get(v_x_159_, 1);
lean_inc(v_target_161_);
v_method_162_ = lean_ctor_get_uint8(v_x_159_, sizeof(void*)*3);
v_headers_163_ = lean_ctor_get(v_x_159_, 2);
lean_inc_ref(v_headers_163_);
v_bodyAction_164_ = lean_ctor_get_uint8(v_x_159_, sizeof(void*)*3 + 1);
v_isCrossOrigin_165_ = lean_ctor_get_uint8(v_x_159_, sizeof(void*)*3 + 2);
lean_dec_ref(v_x_159_);
v___x_166_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__5));
v___x_167_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__6));
v___x_168_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__7);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = l_Std_Http_URI_instReprOrigin_repr___redArg(v_origin_160_);
v___x_171_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_168_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = 0;
v___x_173_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_173_, 0, v___x_171_);
lean_ctor_set_uint8(v___x_173_, sizeof(void*)*1, v___x_172_);
v___x_174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_167_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__9));
v___x_176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = lean_box(1);
v___x_178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__11));
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_178_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_166_);
v___x_182_ = l_Std_Http_instReprRequestTarget_repr(v_target_161_, v___x_169_);
v___x_183_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_168_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*1, v___x_172_);
v___x_185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_181_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_175_);
v___x_187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v___x_177_);
v___x_188_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__13));
v___x_189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v___x_166_);
v___x_191_ = l_Std_Http_instReprMethod_repr(v_method_162_, v___x_169_);
v___x_192_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_168_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*1, v___x_172_);
v___x_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_190_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_175_);
v___x_196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_177_);
v___x_197_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__15));
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_166_);
v___x_200_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__16);
v___x_201_ = l_Std_Http_instReprHeaders_repr___redArg(v_headers_163_);
v___x_202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_200_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*1, v___x_172_);
v___x_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_199_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_175_);
v___x_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_177_);
v___x_207_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__18));
v___x_208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_206_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_166_);
v___x_210_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__19);
v___x_211_ = l_Std_Http_Protocol_H1_instReprRedirectBodyAction_repr(v_bodyAction_164_, v___x_169_);
v___x_212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set_uint8(v___x_213_, sizeof(void*)*1, v___x_172_);
v___x_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_209_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_175_);
v___x_216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_177_);
v___x_217_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__21));
v___x_218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_166_);
v___x_220_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__22);
v___x_221_ = l_Bool_repr___redArg(v_isCrossOrigin_165_);
v___x_222_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*1, v___x_172_);
v___x_224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_219_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = lean_obj_once(&l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25, &l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25_once, _init_l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__25);
v___x_226_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__26));
v___x_227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v___x_224_);
v___x_228_ = ((lean_object*)(l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg___closed__27));
v___x_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_225_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*1, v___x_172_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr(lean_object* v_x_232_, lean_object* v_prec_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___redArg(v_x_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_instReprRedirectPlan_repr___boxed(lean_object* v_x_235_, lean_object* v_prec_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Std_Http_Protocol_H1_instReprRedirectPlan_repr(v_x_235_, v_prec_236_);
lean_dec(v_prec_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx(lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_240_) == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_unsigned_to_nat(0u);
return v___x_241_;
}
else
{
lean_object* v___x_242_; 
v___x_242_ = lean_unsigned_to_nat(1u);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx___boxed(lean_object* v_x_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorIdx(v_x_243_);
lean_dec(v_x_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(lean_object* v_t_245_, lean_object* v_k_246_){
_start:
{
if (lean_obj_tag(v_t_245_) == 0)
{
return v_k_246_;
}
else
{
lean_object* v_plan_247_; lean_object* v___x_248_; 
v_plan_247_ = lean_ctor_get(v_t_245_, 0);
lean_inc_ref(v_plan_247_);
lean_dec_ref_known(v_t_245_, 1);
v___x_248_ = lean_apply_1(v_k_246_, v_plan_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim(lean_object* v_motive_249_, lean_object* v_ctorIdx_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_k_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_251_, v_k_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___boxed(lean_object* v_motive_255_, lean_object* v_ctorIdx_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_k_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim(v_motive_255_, v_ctorIdx_256_, v_t_257_, v_h_258_, v_k_259_);
lean_dec(v_ctorIdx_256_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_done_elim___redArg(lean_object* v_t_261_, lean_object* v_done_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_261_, v_done_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_done_elim(lean_object* v_motive_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_done_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_265_, v_done_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_follow_elim___redArg(lean_object* v_t_269_, lean_object* v_follow_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_269_, v_follow_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_RedirectOutcome_follow_elim(lean_object* v_motive_272_, lean_object* v_t_273_, lean_object* v_h_274_, lean_object* v_follow_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Std_Http_Protocol_H1_RedirectOutcome_ctorElim___redArg(v_t_273_, v_follow_275_);
return v___x_276_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome_default(void){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_box(0);
return v___x_277_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_instInhabitedRedirectOutcome(void){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_box(0);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(lean_object* v_current_279_, lean_object* v_x_280_){
_start:
{
if (lean_obj_tag(v_x_280_) == 0)
{
lean_object* v_uri_281_; lean_object* v_authority_282_; 
lean_dec_ref(v_current_279_);
v_uri_281_ = lean_ctor_get(v_x_280_, 0);
lean_inc_ref(v_uri_281_);
lean_dec_ref_known(v_x_280_, 1);
v_authority_282_ = lean_ctor_get(v_uri_281_, 1);
lean_inc(v_authority_282_);
if (lean_obj_tag(v_authority_282_) == 0)
{
lean_object* v___x_283_; 
lean_dec_ref(v_uri_281_);
v___x_283_ = lean_box(0);
return v___x_283_;
}
else
{
lean_object* v_val_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_299_; 
v_val_284_ = lean_ctor_get(v_authority_282_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_authority_282_);
if (v_isSharedCheck_299_ == 0)
{
v___x_286_ = v_authority_282_;
v_isShared_287_ = v_isSharedCheck_299_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_val_284_);
lean_dec(v_authority_282_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_299_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v_scheme_288_; lean_object* v_host_289_; lean_object* v_port_290_; uint16_t v___y_292_; 
v_scheme_288_ = lean_ctor_get(v_uri_281_, 0);
lean_inc_ref(v_scheme_288_);
lean_dec_ref(v_uri_281_);
v_host_289_ = lean_ctor_get(v_val_284_, 1);
lean_inc_ref(v_host_289_);
v_port_290_ = lean_ctor_get(v_val_284_, 2);
lean_inc(v_port_290_);
lean_dec(v_val_284_);
if (lean_obj_tag(v_port_290_) == 2)
{
uint16_t v_port_297_; 
v_port_297_ = lean_ctor_get_uint16(v_port_290_, 0);
lean_dec_ref_known(v_port_290_, 0);
v___y_292_ = v_port_297_;
goto v___jp_291_;
}
else
{
uint16_t v___x_298_; 
lean_dec(v_port_290_);
v___x_298_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_288_);
v___y_292_ = v___x_298_;
goto v___jp_291_;
}
v___jp_291_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_293_, 0, v_scheme_288_);
lean_ctor_set(v___x_293_, 1, v_host_289_);
lean_ctor_set_uint16(v___x_293_, sizeof(void*)*2, v___y_292_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_293_);
v___x_295_ = v___x_286_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
else
{
lean_object* v_ref_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_332_; 
v_ref_300_ = lean_ctor_get(v_x_280_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v_x_280_);
if (v_isSharedCheck_332_ == 0)
{
v___x_302_ = v_x_280_;
v_isShared_303_ = v_isSharedCheck_332_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_ref_300_);
lean_dec(v_x_280_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_332_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_authority_304_; 
v_authority_304_ = lean_ctor_get(v_ref_300_, 0);
lean_inc(v_authority_304_);
lean_dec_ref(v_ref_300_);
if (lean_obj_tag(v_authority_304_) == 1)
{
lean_object* v_val_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_328_; 
lean_del_object(v___x_302_);
v_val_305_ = lean_ctor_get(v_authority_304_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v_authority_304_);
if (v_isSharedCheck_328_ == 0)
{
v___x_307_ = v_authority_304_;
v_isShared_308_ = v_isSharedCheck_328_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_val_305_);
lean_dec(v_authority_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_328_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v_host_309_; lean_object* v_port_310_; uint16_t v___y_312_; 
v_host_309_ = lean_ctor_get(v_val_305_, 1);
lean_inc_ref(v_host_309_);
v_port_310_ = lean_ctor_get(v_val_305_, 2);
lean_inc(v_port_310_);
lean_dec(v_val_305_);
if (lean_obj_tag(v_port_310_) == 2)
{
uint16_t v_port_325_; 
v_port_325_ = lean_ctor_get_uint16(v_port_310_, 0);
lean_dec_ref_known(v_port_310_, 0);
v___y_312_ = v_port_325_;
goto v___jp_311_;
}
else
{
lean_object* v_scheme_326_; uint16_t v___x_327_; 
lean_dec(v_port_310_);
v_scheme_326_ = lean_ctor_get(v_current_279_, 0);
v___x_327_ = l_Std_Http_URI_Scheme_defaultPort(v_scheme_326_);
v___y_312_ = v___x_327_;
goto v___jp_311_;
}
v___jp_311_:
{
lean_object* v_scheme_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_323_; 
v_scheme_313_ = lean_ctor_get(v_current_279_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v_current_279_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; 
v_unused_324_ = lean_ctor_get(v_current_279_, 1);
lean_dec(v_unused_324_);
v___x_315_ = v_current_279_;
v_isShared_316_ = v_isSharedCheck_323_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_scheme_313_);
lean_dec(v_current_279_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_323_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v_host_309_);
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_scheme_313_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_host_309_);
v___x_318_ = v_reuseFailAlloc_322_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_320_; 
lean_ctor_set_uint16(v___x_318_, sizeof(void*)*2, v___y_312_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_318_);
v___x_320_ = v___x_307_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
}
else
{
lean_object* v___x_330_; 
lean_dec(v_authority_304_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v_current_279_);
v___x_330_ = v___x_302_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_current_279_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(uint8_t v_originalMethod_333_, uint8_t v_responseVersion_334_, lean_object* v_x_335_){
_start:
{
uint8_t v___y_337_; 
switch(lean_obj_tag(v_x_335_))
{
case 17:
{
uint8_t v___x_344_; uint8_t v___x_345_; 
v___x_344_ = 9;
v___x_345_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_333_, v___x_344_);
if (v___x_345_ == 0)
{
uint8_t v___x_346_; 
v___x_346_ = 8;
return v___x_346_;
}
else
{
return v___x_344_;
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
return v_originalMethod_333_;
}
}
v___jp_336_:
{
if (v___y_337_ == 0)
{
return v_originalMethod_333_;
}
else
{
uint8_t v___x_338_; 
v___x_338_ = 8;
return v___x_338_;
}
}
v___jp_339_:
{
uint8_t v___x_340_; uint8_t v___x_341_; 
v___x_340_ = 23;
v___x_341_ = l_Std_Http_instBEqMethod_beq(v_originalMethod_333_, v___x_340_);
if (v___x_341_ == 0)
{
v___y_337_ = v___x_341_;
goto v___jp_336_;
}
else
{
uint8_t v___x_342_; uint8_t v___x_343_; 
v___x_342_ = 0;
v___x_343_ = l_Std_Http_instBEqVersion_beq(v_responseVersion_334_, v___x_342_);
if (v___x_343_ == 0)
{
v___y_337_ = v___x_341_;
goto v___jp_336_;
}
else
{
return v_originalMethod_333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod___boxed(lean_object* v_originalMethod_347_, lean_object* v_responseVersion_348_, lean_object* v_x_349_){
_start:
{
uint8_t v_originalMethod_boxed_350_; uint8_t v_responseVersion_boxed_351_; uint8_t v_res_352_; lean_object* v_r_353_; 
v_originalMethod_boxed_350_ = lean_unbox(v_originalMethod_347_);
v_responseVersion_boxed_351_ = lean_unbox(v_responseVersion_348_);
v_res_352_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_originalMethod_boxed_350_, v_responseVersion_boxed_351_, v_x_349_);
lean_dec(v_x_349_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_354_ = l_Std_Http_Header_Name_transferEncoding;
v___x_355_ = l_Std_Http_Header_Name_keepAlive;
v___x_356_ = l_Std_Http_Header_Name_connection;
v___x_357_ = lean_unsigned_to_nat(3u);
v___x_358_ = lean_mk_empty_array_with_capacity(v___x_357_);
v___x_359_ = lean_array_push(v___x_358_, v___x_356_);
v___x_360_ = lean_array_push(v___x_359_, v___x_355_);
v___x_361_ = lean_array_push(v___x_360_, v___x_354_);
return v___x_361_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders(void){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders___closed__0);
return v___x_362_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(lean_object* v_a_363_, lean_object* v_x_364_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
uint8_t v___x_365_; 
v___x_365_ = 0;
return v___x_365_;
}
else
{
lean_object* v_key_366_; lean_object* v_tail_367_; uint8_t v___x_368_; 
v_key_366_ = lean_ctor_get(v_x_364_, 0);
v_tail_367_ = lean_ctor_get(v_x_364_, 2);
v___x_368_ = lean_string_dec_eq(v_key_366_, v_a_363_);
if (v___x_368_ == 0)
{
v_x_364_ = v_tail_367_;
goto _start;
}
else
{
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg___boxed(lean_object* v_a_370_, lean_object* v_x_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_370_, v_x_371_);
lean_dec(v_x_371_);
lean_dec_ref(v_a_370_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(lean_object* v_m_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_buckets_376_; lean_object* v___x_377_; uint64_t v___x_378_; uint64_t v___x_379_; uint64_t v___x_380_; uint64_t v_fold_381_; uint64_t v___x_382_; uint64_t v___x_383_; uint64_t v___x_384_; size_t v___x_385_; size_t v___x_386_; size_t v___x_387_; size_t v___x_388_; size_t v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v_buckets_376_ = lean_ctor_get(v_m_374_, 1);
v___x_377_ = lean_array_get_size(v_buckets_376_);
v___x_378_ = lean_string_hash(v_a_375_);
v___x_379_ = 32ULL;
v___x_380_ = lean_uint64_shift_right(v___x_378_, v___x_379_);
v_fold_381_ = lean_uint64_xor(v___x_378_, v___x_380_);
v___x_382_ = 16ULL;
v___x_383_ = lean_uint64_shift_right(v_fold_381_, v___x_382_);
v___x_384_ = lean_uint64_xor(v_fold_381_, v___x_383_);
v___x_385_ = lean_uint64_to_usize(v___x_384_);
v___x_386_ = lean_usize_of_nat(v___x_377_);
v___x_387_ = ((size_t)1ULL);
v___x_388_ = lean_usize_sub(v___x_386_, v___x_387_);
v___x_389_ = lean_usize_land(v___x_385_, v___x_388_);
v___x_390_ = lean_array_uget_borrowed(v_buckets_376_, v___x_389_);
v___x_391_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_375_, v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg___boxed(lean_object* v_m_392_, lean_object* v_a_393_){
_start:
{
uint8_t v_res_394_; lean_object* v_r_395_; 
v_res_394_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_m_392_, v_a_393_);
lean_dec_ref(v_a_393_);
lean_dec_ref(v_m_392_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(lean_object* v_a_396_, lean_object* v_x_397_){
_start:
{
lean_object* v_key_398_; lean_object* v_value_399_; lean_object* v_tail_400_; uint8_t v___x_401_; 
v_key_398_ = lean_ctor_get(v_x_397_, 0);
v_value_399_ = lean_ctor_get(v_x_397_, 1);
v_tail_400_ = lean_ctor_get(v_x_397_, 2);
v___x_401_ = lean_string_dec_eq(v_key_398_, v_a_396_);
if (v___x_401_ == 0)
{
v_x_397_ = v_tail_400_;
goto _start;
}
else
{
lean_inc(v_value_399_);
return v_value_399_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg___boxed(lean_object* v_a_403_, lean_object* v_x_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(v_a_403_, v_x_404_);
lean_dec(v_x_404_);
lean_dec_ref(v_a_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(lean_object* v_m_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_buckets_408_; lean_object* v___x_409_; uint64_t v___x_410_; uint64_t v___x_411_; uint64_t v___x_412_; uint64_t v_fold_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint64_t v___x_416_; size_t v___x_417_; size_t v___x_418_; size_t v___x_419_; size_t v___x_420_; size_t v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_buckets_408_ = lean_ctor_get(v_m_406_, 1);
v___x_409_ = lean_array_get_size(v_buckets_408_);
v___x_410_ = lean_string_hash(v_a_407_);
v___x_411_ = 32ULL;
v___x_412_ = lean_uint64_shift_right(v___x_410_, v___x_411_);
v_fold_413_ = lean_uint64_xor(v___x_410_, v___x_412_);
v___x_414_ = 16ULL;
v___x_415_ = lean_uint64_shift_right(v_fold_413_, v___x_414_);
v___x_416_ = lean_uint64_xor(v_fold_413_, v___x_415_);
v___x_417_ = lean_uint64_to_usize(v___x_416_);
v___x_418_ = lean_usize_of_nat(v___x_409_);
v___x_419_ = ((size_t)1ULL);
v___x_420_ = lean_usize_sub(v___x_418_, v___x_419_);
v___x_421_ = lean_usize_land(v___x_417_, v___x_420_);
v___x_422_ = lean_array_uget_borrowed(v_buckets_408_, v___x_421_);
v___x_423_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(v_a_407_, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg___boxed(lean_object* v_m_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_m_424_, v_a_425_);
lean_dec_ref(v_a_425_);
lean_dec_ref(v_m_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(lean_object* v_as_427_, size_t v_i_428_, size_t v_stop_429_, lean_object* v_b_430_){
_start:
{
lean_object* v___y_432_; uint8_t v___x_436_; 
v___x_436_ = lean_usize_dec_eq(v_i_428_, v_stop_429_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_array_uget_borrowed(v_as_427_, v_i_428_);
lean_inc(v___x_437_);
v___x_438_ = l_Std_Http_Header_Name_ofString_x3f(v___x_437_);
if (lean_obj_tag(v___x_438_) == 0)
{
v___y_432_ = v_b_430_;
goto v___jp_431_;
}
else
{
lean_object* v_val_439_; lean_object* v___x_440_; 
v_val_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_val_439_);
lean_dec_ref_known(v___x_438_, 1);
v___x_440_ = lean_array_push(v_b_430_, v_val_439_);
v___y_432_ = v___x_440_;
goto v___jp_431_;
}
}
else
{
return v_b_430_;
}
v___jp_431_:
{
size_t v___x_433_; size_t v___x_434_; 
v___x_433_ = ((size_t)1ULL);
v___x_434_ = lean_usize_add(v_i_428_, v___x_433_);
v_i_428_ = v___x_434_;
v_b_430_ = v___y_432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0___boxed(lean_object* v_as_441_, lean_object* v_i_442_, lean_object* v_stop_443_, lean_object* v_b_444_){
_start:
{
size_t v_i_boxed_445_; size_t v_stop_boxed_446_; lean_object* v_res_447_; 
v_i_boxed_445_ = lean_unbox_usize(v_i_442_);
lean_dec(v_i_442_);
v_stop_boxed_446_ = lean_unbox_usize(v_stop_443_);
lean_dec(v_stop_443_);
v_res_447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_as_441_, v_i_boxed_445_, v_stop_boxed_446_, v_b_444_);
lean_dec_ref(v_as_441_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(lean_object* v_as_448_, size_t v_i_449_, size_t v_stop_450_, lean_object* v_b_451_){
_start:
{
lean_object* v___y_453_; uint8_t v___x_457_; 
v___x_457_ = lean_usize_dec_eq(v_i_449_, v_stop_450_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_array_uget_borrowed(v_as_448_, v_i_449_);
lean_inc(v___x_458_);
v___x_459_ = l_Std_Http_Header_Connection_parse(v___x_458_);
if (lean_obj_tag(v___x_459_) == 0)
{
v___y_453_ = v_b_451_;
goto v___jp_452_;
}
else
{
lean_object* v_val_460_; lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v_val_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_val_460_);
lean_dec_ref_known(v___x_459_, 1);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_array_get_size(v_val_460_);
v___x_463_ = lean_nat_dec_lt(v___x_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_dec(v_val_460_);
v___y_453_ = v_b_451_;
goto v___jp_452_;
}
else
{
uint8_t v___x_464_; 
v___x_464_ = lean_nat_dec_le(v___x_462_, v___x_462_);
if (v___x_464_ == 0)
{
if (v___x_463_ == 0)
{
lean_dec(v_val_460_);
v___y_453_ = v_b_451_;
goto v___jp_452_;
}
else
{
size_t v___x_465_; size_t v___x_466_; lean_object* v___x_467_; 
v___x_465_ = ((size_t)0ULL);
v___x_466_ = lean_usize_of_nat(v___x_462_);
v___x_467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_val_460_, v___x_465_, v___x_466_, v_b_451_);
lean_dec(v_val_460_);
v___y_453_ = v___x_467_;
goto v___jp_452_;
}
}
else
{
size_t v___x_468_; size_t v___x_469_; lean_object* v___x_470_; 
v___x_468_ = ((size_t)0ULL);
v___x_469_ = lean_usize_of_nat(v___x_462_);
v___x_470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__0(v_val_460_, v___x_468_, v___x_469_, v_b_451_);
lean_dec(v_val_460_);
v___y_453_ = v___x_470_;
goto v___jp_452_;
}
}
}
}
else
{
return v_b_451_;
}
v___jp_452_:
{
size_t v___x_454_; size_t v___x_455_; 
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_add(v_i_449_, v___x_454_);
v_i_449_ = v___x_455_;
v_b_451_ = v___y_453_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4___boxed(lean_object* v_as_471_, lean_object* v_i_472_, lean_object* v_stop_473_, lean_object* v_b_474_){
_start:
{
size_t v_i_boxed_475_; size_t v_stop_boxed_476_; lean_object* v_res_477_; 
v_i_boxed_475_ = lean_unbox_usize(v_i_472_);
lean_dec(v_i_472_);
v_stop_boxed_476_ = lean_unbox_usize(v_stop_473_);
lean_dec(v_stop_473_);
v_res_477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(v_as_471_, v_i_boxed_475_, v_stop_boxed_476_, v_b_474_);
lean_dec_ref(v_as_471_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(lean_object* v___x_478_, lean_object* v___x_479_, size_t v_sz_480_, size_t v_i_481_, lean_object* v_bs_482_){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = lean_usize_dec_lt(v_i_481_, v_sz_480_);
if (v___x_483_ == 0)
{
return v_bs_482_;
}
else
{
lean_object* v_entries_484_; lean_object* v___x_485_; lean_object* v_bs_x27_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v_snd_490_; size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
v_entries_484_ = lean_ctor_get(v___x_478_, 0);
v___x_485_ = lean_unsigned_to_nat(0u);
v_bs_x27_486_ = lean_array_uset(v_bs_482_, v_i_481_, v___x_485_);
v___x_487_ = lean_usize_to_nat(v_i_481_);
v___x_488_ = lean_array_fget_borrowed(v___x_479_, v___x_487_);
lean_dec(v___x_487_);
v___x_489_ = lean_array_fget_borrowed(v_entries_484_, v___x_488_);
v_snd_490_ = lean_ctor_get(v___x_489_, 1);
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_add(v_i_481_, v___x_491_);
lean_inc(v_snd_490_);
v___x_493_ = lean_array_uset(v_bs_x27_486_, v_i_481_, v_snd_490_);
v_i_481_ = v___x_492_;
v_bs_482_ = v___x_493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg___boxed(lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v_sz_497_, lean_object* v_i_498_, lean_object* v_bs_499_){
_start:
{
size_t v_sz_boxed_500_; size_t v_i_boxed_501_; lean_object* v_res_502_; 
v_sz_boxed_500_ = lean_unbox_usize(v_sz_497_);
lean_dec(v_sz_497_);
v_i_boxed_501_ = lean_unbox_usize(v_i_498_);
lean_dec(v_i_498_);
v_res_502_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(v___x_495_, v___x_496_, v_sz_boxed_500_, v_i_boxed_501_, v_bs_499_);
lean_dec_ref(v___x_496_);
lean_dec_ref(v___x_495_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(lean_object* v_headers_505_){
_start:
{
lean_object* v_indexes_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_indexes_506_ = lean_ctor_get(v_headers_505_, 1);
v___x_507_ = l_Std_Http_Header_Name_connection;
v___x_508_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
v___x_509_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
return v___x_509_;
}
else
{
lean_object* v___x_510_; size_t v_sz_511_; size_t v___x_512_; lean_object* v_entries_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_510_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_indexes_506_, v___x_507_);
v_sz_511_ = lean_array_size(v___x_510_);
v___x_512_ = ((size_t)0ULL);
lean_inc(v___x_510_);
v_entries_513_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(v_headers_505_, v___x_510_, v_sz_511_, v___x_512_, v___x_510_);
lean_dec(v___x_510_);
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = ((lean_object*)(l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___closed__0));
v___x_516_ = lean_array_get_size(v_entries_513_);
v___x_517_ = lean_nat_dec_lt(v___x_514_, v___x_516_);
if (v___x_517_ == 0)
{
lean_dec_ref(v_entries_513_);
return v___x_515_;
}
else
{
uint8_t v___x_518_; 
v___x_518_ = lean_nat_dec_le(v___x_516_, v___x_516_);
if (v___x_518_ == 0)
{
if (v___x_517_ == 0)
{
lean_dec_ref(v_entries_513_);
return v___x_515_;
}
else
{
size_t v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_usize_of_nat(v___x_516_);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(v_entries_513_, v___x_512_, v___x_519_, v___x_515_);
lean_dec_ref(v_entries_513_);
return v___x_520_;
}
}
else
{
size_t v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_usize_of_nat(v___x_516_);
v___x_522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__4(v_entries_513_, v___x_512_, v___x_521_, v___x_515_);
lean_dec_ref(v_entries_513_);
return v___x_522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders___boxed(lean_object* v_headers_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_523_);
lean_dec_ref(v_headers_523_);
return v_res_524_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(lean_object* v_00_u03b2_525_, lean_object* v_m_526_, lean_object* v_a_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_m_526_, v_a_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___boxed(lean_object* v_00_u03b2_529_, lean_object* v_m_530_, lean_object* v_a_531_){
_start:
{
uint8_t v_res_532_; lean_object* v_r_533_; 
v_res_532_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1(v_00_u03b2_529_, v_m_530_, v_a_531_);
lean_dec_ref(v_a_531_);
lean_dec_ref(v_m_530_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(lean_object* v_00_u03b2_534_, lean_object* v_m_535_, lean_object* v_a_536_, lean_object* v_hma_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_m_535_, v_a_536_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___boxed(lean_object* v_00_u03b2_539_, lean_object* v_m_540_, lean_object* v_a_541_, lean_object* v_hma_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2(v_00_u03b2_539_, v_m_540_, v_a_541_, v_hma_542_);
lean_dec_ref(v_a_541_);
lean_dec_ref(v_m_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(lean_object* v___x_544_, lean_object* v___x_545_, lean_object* v_as_546_, size_t v_sz_547_, size_t v_i_548_, lean_object* v_bs_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___redArg(v___x_544_, v___x_545_, v_sz_547_, v_i_548_, v_bs_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3___boxed(lean_object* v___x_551_, lean_object* v___x_552_, lean_object* v_as_553_, lean_object* v_sz_554_, lean_object* v_i_555_, lean_object* v_bs_556_){
_start:
{
size_t v_sz_boxed_557_; size_t v_i_boxed_558_; lean_object* v_res_559_; 
v_sz_boxed_557_ = lean_unbox_usize(v_sz_554_);
lean_dec(v_sz_554_);
v_i_boxed_558_ = lean_unbox_usize(v_i_555_);
lean_dec(v_i_555_);
v_res_559_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__3(v___x_551_, v___x_552_, v_as_553_, v_sz_boxed_557_, v_i_boxed_558_, v_bs_556_);
lean_dec_ref(v_as_553_);
lean_dec_ref(v___x_552_);
lean_dec_ref(v___x_551_);
return v_res_559_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(lean_object* v_00_u03b2_560_, lean_object* v_a_561_, lean_object* v_x_562_){
_start:
{
uint8_t v___x_563_; 
v___x_563_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_561_, v_x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___boxed(lean_object* v_00_u03b2_564_, lean_object* v_a_565_, lean_object* v_x_566_){
_start:
{
uint8_t v_res_567_; lean_object* v_r_568_; 
v_res_567_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1(v_00_u03b2_564_, v_a_565_, v_x_566_);
lean_dec(v_x_566_);
lean_dec_ref(v_a_565_);
v_r_568_ = lean_box(v_res_567_);
return v_r_568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3(lean_object* v_00_u03b2_569_, lean_object* v_a_570_, lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___redArg(v_a_570_, v_x_571_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3___boxed(lean_object* v_00_u03b2_574_, lean_object* v_a_575_, lean_object* v_x_576_, lean_object* v_x_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Std_DHashMap_Internal_AssocList_get___at___00Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2_spec__3(v_00_u03b2_574_, v_a_575_, v_x_576_, v_x_577_);
lean_dec(v_x_576_);
lean_dec_ref(v_a_575_);
return v_res_578_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_579_ = l_Std_Http_Header_Name_proxyAuthorization;
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_mk_empty_array_with_capacity(v___x_580_);
v___x_582_ = lean_array_push(v___x_581_, v___x_579_);
return v___x_582_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders(void){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders___closed__0);
return v___x_583_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_584_ = l_Std_Http_Header_Name_referer;
v___x_585_ = l_Std_Http_Header_Name_cookie;
v___x_586_ = l_Std_Http_Header_Name_authorization;
v___x_587_ = lean_unsigned_to_nat(3u);
v___x_588_ = lean_mk_empty_array_with_capacity(v___x_587_);
v___x_589_ = lean_array_push(v___x_588_, v___x_586_);
v___x_590_ = lean_array_push(v___x_589_, v___x_585_);
v___x_591_ = lean_array_push(v___x_590_, v___x_584_);
return v___x_591_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders(void){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders___closed__0);
return v___x_592_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_593_ = l_Std_Http_Header_Name_ifModifiedSince;
v___x_594_ = l_Std_Http_Header_Name_ifNoneMatch;
v___x_595_ = lean_unsigned_to_nat(2u);
v___x_596_ = lean_mk_empty_array_with_capacity(v___x_595_);
v___x_597_ = lean_array_push(v___x_596_, v___x_594_);
v___x_598_ = lean_array_push(v___x_597_, v___x_593_);
return v___x_598_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders(void){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders___closed__0);
return v___x_599_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_600_ = l_Std_Http_Header_Name_lastModified;
v___x_601_ = l_Std_Http_Header_Name_contentLocation;
v___x_602_ = l_Std_Http_Header_Name_contentLanguage;
v___x_603_ = l_Std_Http_Header_Name_contentEncoding;
v___x_604_ = l_Std_Http_Header_Name_contentLength;
v___x_605_ = l_Std_Http_Header_Name_contentType;
v___x_606_ = lean_unsigned_to_nat(6u);
v___x_607_ = lean_mk_empty_array_with_capacity(v___x_606_);
v___x_608_ = lean_array_push(v___x_607_, v___x_605_);
v___x_609_ = lean_array_push(v___x_608_, v___x_604_);
v___x_610_ = lean_array_push(v___x_609_, v___x_603_);
v___x_611_ = lean_array_push(v___x_610_, v___x_602_);
v___x_612_ = lean_array_push(v___x_611_, v___x_601_);
v___x_613_ = lean_array_push(v___x_612_, v___x_600_);
return v___x_613_;
}
}
static lean_object* _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders(void){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = lean_obj_once(&l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0, &l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0_once, _init_l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders___closed__0);
return v___x_614_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = lean_box(0);
v___x_618_ = lean_unsigned_to_nat(16u);
v___x_619_ = lean_mk_array(v___x_618_, v___x_617_);
return v___x_619_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__1);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v___x_620_);
return v___x_622_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__2);
v___x_624_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__0));
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg(){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___closed__3);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg___boxed(lean_object* v___dummy_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg();
return v_res_629_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0(void){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___redArg();
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2(lean_object* v_00_u03b2_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3___lam__0(lean_object* v_i_633_, lean_object* v_x_634_){
_start:
{
if (lean_obj_tag(v_x_634_) == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = lean_mk_empty_array_with_capacity(v___x_635_);
v___x_637_ = lean_array_push(v___x_636_, v_i_633_);
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
else
{
lean_object* v_val_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_647_; 
v_val_639_ = lean_ctor_get(v_x_634_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_x_634_);
if (v_isSharedCheck_647_ == 0)
{
v___x_641_ = v_x_634_;
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_val_639_);
lean_dec(v_x_634_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = lean_array_push(v_val_639_, v_i_633_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_643_);
v___x_645_ = v___x_641_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3(lean_object* v_i_648_, lean_object* v_a_649_, lean_object* v_x_650_){
_start:
{
if (lean_obj_tag(v_x_650_) == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v_val_653_; lean_object* v___x_654_; 
v___x_651_ = lean_box(0);
v___x_652_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3___lam__0(v_i_648_, v___x_651_);
v_val_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_val_653_);
lean_dec(v___x_652_);
v___x_654_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_654_, 0, v_a_649_);
lean_ctor_set(v___x_654_, 1, v_val_653_);
lean_ctor_set(v___x_654_, 2, v_x_650_);
return v___x_654_;
}
else
{
lean_object* v_key_655_; lean_object* v_value_656_; lean_object* v_tail_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_672_; 
v_key_655_ = lean_ctor_get(v_x_650_, 0);
v_value_656_ = lean_ctor_get(v_x_650_, 1);
v_tail_657_ = lean_ctor_get(v_x_650_, 2);
v_isSharedCheck_672_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_672_ == 0)
{
v___x_659_ = v_x_650_;
v_isShared_660_ = v_isSharedCheck_672_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_tail_657_);
lean_inc(v_value_656_);
lean_inc(v_key_655_);
lean_dec(v_x_650_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_672_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
uint8_t v___x_661_; 
v___x_661_ = lean_string_dec_eq(v_key_655_, v_a_649_);
if (v___x_661_ == 0)
{
lean_object* v_tail_662_; lean_object* v___x_664_; 
v_tail_662_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3(v_i_648_, v_a_649_, v_tail_657_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 2, v_tail_662_);
v___x_664_ = v___x_659_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_key_655_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_value_656_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v_tail_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v_val_668_; lean_object* v___x_670_; 
lean_dec(v_key_655_);
v___x_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_666_, 0, v_value_656_);
v___x_667_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3___lam__0(v_i_648_, v___x_666_);
v_val_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_val_668_);
lean_dec(v___x_667_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v_val_668_);
lean_ctor_set(v___x_659_, 0, v_a_649_);
v___x_670_ = v___x_659_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_649_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_val_668_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_tail_657_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
if (lean_obj_tag(v_x_674_) == 0)
{
return v_x_673_;
}
else
{
lean_object* v_key_675_; lean_object* v_value_676_; lean_object* v_tail_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_700_; 
v_key_675_ = lean_ctor_get(v_x_674_, 0);
v_value_676_ = lean_ctor_get(v_x_674_, 1);
v_tail_677_ = lean_ctor_get(v_x_674_, 2);
v_isSharedCheck_700_ = !lean_is_exclusive(v_x_674_);
if (v_isSharedCheck_700_ == 0)
{
v___x_679_ = v_x_674_;
v_isShared_680_ = v_isSharedCheck_700_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_tail_677_);
lean_inc(v_value_676_);
lean_inc(v_key_675_);
lean_dec(v_x_674_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_700_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; uint64_t v___x_682_; uint64_t v___x_683_; uint64_t v___x_684_; uint64_t v_fold_685_; uint64_t v___x_686_; uint64_t v___x_687_; uint64_t v___x_688_; size_t v___x_689_; size_t v___x_690_; size_t v___x_691_; size_t v___x_692_; size_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_681_ = lean_array_get_size(v_x_673_);
v___x_682_ = lean_string_hash(v_key_675_);
v___x_683_ = 32ULL;
v___x_684_ = lean_uint64_shift_right(v___x_682_, v___x_683_);
v_fold_685_ = lean_uint64_xor(v___x_682_, v___x_684_);
v___x_686_ = 16ULL;
v___x_687_ = lean_uint64_shift_right(v_fold_685_, v___x_686_);
v___x_688_ = lean_uint64_xor(v_fold_685_, v___x_687_);
v___x_689_ = lean_uint64_to_usize(v___x_688_);
v___x_690_ = lean_usize_of_nat(v___x_681_);
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_sub(v___x_690_, v___x_691_);
v___x_693_ = lean_usize_land(v___x_689_, v___x_692_);
v___x_694_ = lean_array_uget_borrowed(v_x_673_, v___x_693_);
lean_inc(v___x_694_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 2, v___x_694_);
v___x_696_ = v___x_679_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_key_675_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_value_676_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v___x_694_);
v___x_696_ = v_reuseFailAlloc_699_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; 
v___x_697_ = lean_array_uset(v_x_673_, v___x_693_, v___x_696_);
v_x_673_ = v___x_697_;
v_x_674_ = v_tail_677_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4___redArg(lean_object* v_i_701_, lean_object* v_source_702_, lean_object* v_target_703_){
_start:
{
lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_704_ = lean_array_get_size(v_source_702_);
v___x_705_ = lean_nat_dec_lt(v_i_701_, v___x_704_);
if (v___x_705_ == 0)
{
lean_dec_ref(v_source_702_);
lean_dec(v_i_701_);
return v_target_703_;
}
else
{
lean_object* v_es_706_; lean_object* v___x_707_; lean_object* v_source_708_; lean_object* v_target_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_es_706_ = lean_array_fget(v_source_702_, v_i_701_);
v___x_707_ = lean_box(0);
v_source_708_ = lean_array_fset(v_source_702_, v_i_701_, v___x_707_);
v_target_709_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6___redArg(v_target_703_, v_es_706_);
v___x_710_ = lean_unsigned_to_nat(1u);
v___x_711_ = lean_nat_add(v_i_701_, v___x_710_);
lean_dec(v_i_701_);
v_i_701_ = v___x_711_;
v_source_702_ = v_source_708_;
v_target_703_ = v_target_709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2___redArg(lean_object* v_data_713_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_nbuckets_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_714_ = lean_array_get_size(v_data_713_);
v___x_715_ = lean_unsigned_to_nat(2u);
v_nbuckets_716_ = lean_nat_mul(v___x_714_, v___x_715_);
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = lean_box(0);
v___x_719_ = lean_mk_array(v_nbuckets_716_, v___x_718_);
v___x_720_ = lean_array_propagate_mark(v_data_713_, v___x_719_);
v___x_721_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4___redArg(v___x_717_, v_data_713_, v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(lean_object* v_i_722_, lean_object* v_m_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_size_725_; lean_object* v_buckets_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_776_; 
v_size_725_ = lean_ctor_get(v_m_723_, 0);
v_buckets_726_ = lean_ctor_get(v_m_723_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_m_723_);
if (v_isSharedCheck_776_ == 0)
{
v___x_728_ = v_m_723_;
v_isShared_729_ = v_isSharedCheck_776_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_buckets_726_);
lean_inc(v_size_725_);
lean_dec(v_m_723_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_776_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; uint64_t v___x_731_; uint64_t v___x_732_; uint64_t v___x_733_; uint64_t v_fold_734_; uint64_t v___x_735_; uint64_t v___x_736_; uint64_t v___x_737_; size_t v___x_738_; size_t v___x_739_; size_t v___x_740_; size_t v___x_741_; size_t v___x_742_; lean_object* v_bkt_743_; uint8_t v___x_744_; 
v___x_730_ = lean_array_get_size(v_buckets_726_);
v___x_731_ = lean_string_hash(v_a_724_);
v___x_732_ = 32ULL;
v___x_733_ = lean_uint64_shift_right(v___x_731_, v___x_732_);
v_fold_734_ = lean_uint64_xor(v___x_731_, v___x_733_);
v___x_735_ = 16ULL;
v___x_736_ = lean_uint64_shift_right(v_fold_734_, v___x_735_);
v___x_737_ = lean_uint64_xor(v_fold_734_, v___x_736_);
v___x_738_ = lean_uint64_to_usize(v___x_737_);
v___x_739_ = lean_usize_of_nat(v___x_730_);
v___x_740_ = ((size_t)1ULL);
v___x_741_ = lean_usize_sub(v___x_739_, v___x_740_);
v___x_742_ = lean_usize_land(v___x_738_, v___x_741_);
v_bkt_743_ = lean_array_uget_borrowed(v_buckets_726_, v___x_742_);
v___x_744_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_724_, v_bkt_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v_size_x27_748_; lean_object* v___x_749_; lean_object* v_buckets_x27_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_745_ = lean_unsigned_to_nat(1u);
v___x_746_ = lean_mk_empty_array_with_capacity(v___x_745_);
v___x_747_ = lean_array_push(v___x_746_, v_i_722_);
v_size_x27_748_ = lean_nat_add(v_size_725_, v___x_745_);
lean_dec(v_size_725_);
lean_inc(v_bkt_743_);
v___x_749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_749_, 0, v_a_724_);
lean_ctor_set(v___x_749_, 1, v___x_747_);
lean_ctor_set(v___x_749_, 2, v_bkt_743_);
v_buckets_x27_750_ = lean_array_uset(v_buckets_726_, v___x_742_, v___x_749_);
v___x_751_ = lean_unsigned_to_nat(4u);
v___x_752_ = lean_nat_mul(v_size_x27_748_, v___x_751_);
v___x_753_ = lean_unsigned_to_nat(3u);
v___x_754_ = lean_nat_div(v___x_752_, v___x_753_);
lean_dec(v___x_752_);
v___x_755_ = lean_array_get_size(v_buckets_x27_750_);
v___x_756_ = lean_nat_dec_le(v___x_754_, v___x_755_);
lean_dec(v___x_754_);
if (v___x_756_ == 0)
{
lean_object* v_val_757_; lean_object* v___x_759_; 
v_val_757_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2___redArg(v_buckets_x27_750_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v_val_757_);
lean_ctor_set(v___x_728_, 0, v_size_x27_748_);
v___x_759_ = v___x_728_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_size_x27_748_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_val_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
else
{
lean_object* v___x_762_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v_buckets_x27_750_);
lean_ctor_set(v___x_728_, 0, v_size_x27_748_);
v___x_762_ = v___x_728_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_size_x27_748_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_buckets_x27_750_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
else
{
lean_object* v___x_764_; lean_object* v_buckets_x27_765_; lean_object* v_bkt_x27_766_; lean_object* v___y_768_; uint8_t v___x_773_; 
lean_inc(v_bkt_743_);
v___x_764_ = lean_box(0);
v_buckets_x27_765_ = lean_array_uset(v_buckets_726_, v___x_742_, v___x_764_);
lean_inc_ref(v_a_724_);
v_bkt_x27_766_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__3(v_i_722_, v_a_724_, v_bkt_743_);
v___x_773_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1_spec__1___redArg(v_a_724_, v_bkt_x27_766_);
lean_dec_ref(v_a_724_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_unsigned_to_nat(1u);
v___x_775_ = lean_nat_sub(v_size_725_, v___x_774_);
lean_dec(v_size_725_);
v___y_768_ = v___x_775_;
goto v___jp_767_;
}
else
{
v___y_768_ = v_size_725_;
goto v___jp_767_;
}
v___jp_767_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = lean_array_uset(v_buckets_x27_765_, v___x_742_, v_bkt_x27_766_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v___x_769_);
lean_ctor_set(v___x_728_, 0, v___y_768_);
v___x_771_ = v___x_728_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___y_768_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(lean_object* v_a_777_, lean_object* v_as_778_, size_t v_i_779_, size_t v_stop_780_){
_start:
{
uint8_t v___x_781_; 
v___x_781_ = lean_usize_dec_eq(v_i_779_, v_stop_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_782_ = lean_array_uget_borrowed(v_as_778_, v_i_779_);
v___x_783_ = lean_string_dec_eq(v_a_777_, v___x_782_);
if (v___x_783_ == 0)
{
size_t v___x_784_; size_t v___x_785_; 
v___x_784_ = ((size_t)1ULL);
v___x_785_ = lean_usize_add(v_i_779_, v___x_784_);
v_i_779_ = v___x_785_;
goto _start;
}
else
{
return v___x_783_;
}
}
else
{
uint8_t v___x_787_; 
v___x_787_ = 0;
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0___boxed(lean_object* v_a_788_, lean_object* v_as_789_, lean_object* v_i_790_, lean_object* v_stop_791_){
_start:
{
size_t v_i_boxed_792_; size_t v_stop_boxed_793_; uint8_t v_res_794_; lean_object* v_r_795_; 
v_i_boxed_792_ = lean_unbox_usize(v_i_790_);
lean_dec(v_i_790_);
v_stop_boxed_793_ = lean_unbox_usize(v_stop_791_);
lean_dec(v_stop_791_);
v_res_794_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_a_788_, v_as_789_, v_i_boxed_792_, v_stop_boxed_793_);
lean_dec_ref(v_as_789_);
lean_dec_ref(v_a_788_);
v_r_795_ = lean_box(v_res_794_);
return v_r_795_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(lean_object* v_as_796_, lean_object* v_a_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_array_get_size(v_as_796_);
v___x_800_ = lean_nat_dec_lt(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
return v___x_800_;
}
else
{
if (v___x_800_ == 0)
{
return v___x_800_;
}
else
{
size_t v___x_801_; size_t v___x_802_; uint8_t v___x_803_; 
v___x_801_ = ((size_t)0ULL);
v___x_802_ = lean_usize_of_nat(v___x_799_);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0_spec__0(v_a_797_, v_as_796_, v___x_801_, v___x_802_);
return v___x_803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0___boxed(lean_object* v_as_804_, lean_object* v_a_805_){
_start:
{
uint8_t v_res_806_; lean_object* v_r_807_; 
v_res_806_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v_as_804_, v_a_805_);
lean_dec_ref(v_a_805_);
lean_dec_ref(v_as_804_);
v_r_807_ = lean_box(v_res_806_);
return v_r_807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(lean_object* v___y_808_, lean_object* v_as_809_, size_t v_i_810_, size_t v_stop_811_, lean_object* v_b_812_){
_start:
{
lean_object* v___y_814_; uint8_t v___x_818_; 
v___x_818_ = lean_usize_dec_eq(v_i_810_, v_stop_811_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v_fst_820_; uint8_t v___x_834_; 
v___x_819_ = lean_array_uget_borrowed(v_as_809_, v_i_810_);
v_fst_820_ = lean_ctor_get(v___x_819_, 0);
v___x_834_ = l_Array_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__0(v___y_808_, v_fst_820_);
if (v___x_834_ == 0)
{
goto v___jp_821_;
}
else
{
if (v___x_818_ == 0)
{
v___y_814_ = v_b_812_;
goto v___jp_813_;
}
else
{
goto v___jp_821_;
}
}
v___jp_821_:
{
lean_object* v_entries_822_; lean_object* v_indexes_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_833_; 
v_entries_822_ = lean_ctor_get(v_b_812_, 0);
v_indexes_823_ = lean_ctor_get(v_b_812_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v_b_812_);
if (v_isSharedCheck_833_ == 0)
{
v___x_825_ = v_b_812_;
v_isShared_826_ = v_isSharedCheck_833_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_indexes_823_);
lean_inc(v_entries_822_);
lean_dec(v_b_812_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_833_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_i_827_; lean_object* v_entries_828_; lean_object* v_indexes_829_; lean_object* v___x_831_; 
v_i_827_ = lean_array_get_size(v_entries_822_);
lean_inc(v___x_819_);
v_entries_828_ = lean_array_push(v_entries_822_, v___x_819_);
lean_inc(v_fst_820_);
v_indexes_829_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1(v_i_827_, v_indexes_823_, v_fst_820_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v_indexes_829_);
lean_ctor_set(v___x_825_, 0, v_entries_828_);
v___x_831_ = v___x_825_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_entries_828_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_indexes_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
v___y_814_ = v___x_831_;
goto v___jp_813_;
}
}
}
}
else
{
return v_b_812_;
}
v___jp_813_:
{
size_t v___x_815_; size_t v___x_816_; 
v___x_815_ = ((size_t)1ULL);
v___x_816_ = lean_usize_add(v_i_810_, v___x_815_);
v_i_810_ = v___x_816_;
v_b_812_ = v___y_814_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3___boxed(lean_object* v___y_835_, lean_object* v_as_836_, lean_object* v_i_837_, lean_object* v_stop_838_, lean_object* v_b_839_){
_start:
{
size_t v_i_boxed_840_; size_t v_stop_boxed_841_; lean_object* v_res_842_; 
v_i_boxed_840_ = lean_unbox_usize(v_i_837_);
lean_dec(v_i_837_);
v_stop_boxed_841_ = lean_unbox_usize(v_stop_838_);
lean_dec(v_stop_838_);
v_res_842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_835_, v_as_836_, v_i_boxed_840_, v_stop_boxed_841_, v_b_839_);
lean_dec_ref(v_as_836_);
lean_dec_ref(v___y_835_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(lean_object* v_headers_843_, uint8_t v_isCrossOrigin_844_, uint8_t v_methodChanged_845_){
_start:
{
lean_object* v___y_847_; lean_object* v___y_857_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v_afterConnection_864_; 
v___x_862_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_connectionHeaders;
v___x_863_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders(v_headers_843_);
v_afterConnection_864_ = l_Array_append___redArg(v___x_862_, v___x_863_);
lean_dec_ref(v___x_863_);
if (v_isCrossOrigin_844_ == 0)
{
v___y_857_ = v_afterConnection_864_;
goto v___jp_856_;
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_865_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_clientProxyHeaders;
v___x_866_ = l_Array_append___redArg(v_afterConnection_864_, v___x_865_);
v___x_867_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_originHeaders;
v___x_868_ = l_Array_append___redArg(v___x_866_, v___x_867_);
v___x_869_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_870_ = l_Array_append___redArg(v___x_868_, v___x_869_);
v___y_857_ = v___x_870_;
goto v___jp_856_;
}
v___jp_846_:
{
lean_object* v_entries_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_entries_848_ = lean_ctor_get(v_headers_843_, 0);
v___x_849_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0, &l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__2___closed__0);
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = lean_array_get_size(v_entries_848_);
v___x_852_ = lean_nat_dec_lt(v___x_850_, v___x_851_);
if (v___x_852_ == 0)
{
lean_dec_ref(v___y_847_);
return v___x_849_;
}
else
{
size_t v___x_853_; size_t v___x_854_; lean_object* v___x_855_; 
v___x_853_ = ((size_t)0ULL);
v___x_854_ = lean_usize_of_nat(v___x_851_);
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__3(v___y_847_, v_entries_848_, v___x_853_, v___x_854_, v___x_849_);
lean_dec_ref(v___y_847_);
return v___x_855_;
}
}
v___jp_856_:
{
if (v_methodChanged_845_ == 0)
{
v___y_847_ = v___y_857_;
goto v___jp_846_;
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_858_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resourceSpecificHeaders;
v___x_859_ = l_Array_append___redArg(v___y_857_, v___x_858_);
v___x_860_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_validatingHeaders;
v___x_861_ = l_Array_append___redArg(v___x_859_, v___x_860_);
v___y_847_ = v___x_861_;
goto v___jp_846_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders___boxed(lean_object* v_headers_871_, lean_object* v_isCrossOrigin_872_, lean_object* v_methodChanged_873_){
_start:
{
uint8_t v_isCrossOrigin_boxed_874_; uint8_t v_methodChanged_boxed_875_; lean_object* v_res_876_; 
v_isCrossOrigin_boxed_874_ = lean_unbox(v_isCrossOrigin_872_);
v_methodChanged_boxed_875_ = lean_unbox(v_methodChanged_873_);
v_res_876_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v_headers_871_, v_isCrossOrigin_boxed_874_, v_methodChanged_boxed_875_);
lean_dec_ref(v_headers_871_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2(lean_object* v_00_u03b2_877_, lean_object* v_data_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2___redArg(v_data_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_880_, lean_object* v_i_881_, lean_object* v_source_882_, lean_object* v_target_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4___redArg(v_i_881_, v_source_882_, v_target_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_885_, lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders_spec__1_spec__2_spec__4_spec__6___redArg(v_x_886_, v_x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(lean_object* v_headers_889_, lean_object* v_origin_890_){
_start:
{
lean_object* v_entries_891_; lean_object* v_indexes_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v_entries_891_ = lean_ctor_get(v_headers_889_, 0);
v_indexes_892_ = lean_ctor_get(v_headers_889_, 1);
v___x_893_ = l_Std_Http_Header_Name_host;
v___x_894_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_892_, v___x_893_);
if (v___x_894_ == 0)
{
lean_dec_ref(v_origin_890_);
return v_headers_889_;
}
else
{
if (v___x_894_ == 0)
{
lean_dec_ref(v_origin_890_);
return v_headers_889_;
}
else
{
lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_910_; 
lean_inc_ref(v_indexes_892_);
lean_inc_ref(v_entries_891_);
v_isSharedCheck_910_ = !lean_is_exclusive(v_headers_889_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; lean_object* v_unused_912_; 
v_unused_911_ = lean_ctor_get(v_headers_889_, 1);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_headers_889_, 0);
lean_dec(v_unused_912_);
v___x_896_ = v_headers_889_;
v_isShared_897_ = v_isSharedCheck_910_;
goto v_resetjp_895_;
}
else
{
lean_dec(v_headers_889_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_910_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v_idxs_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v_lastIdx_904_; lean_object* v___x_905_; lean_object* v_entries_906_; lean_object* v___x_908_; 
v___x_898_ = l_Std_Http_URI_Origin_hostHeader(v_origin_890_);
v___x_899_ = l_Std_Http_Header_Value_ofString_x21(v___x_898_);
v_idxs_900_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_indexes_892_, v___x_893_);
v___x_901_ = lean_array_get_size(v_idxs_900_);
v___x_902_ = lean_unsigned_to_nat(1u);
v___x_903_ = lean_nat_sub(v___x_901_, v___x_902_);
v_lastIdx_904_ = lean_array_fget(v_idxs_900_, v___x_903_);
lean_dec(v___x_903_);
lean_dec(v_idxs_900_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_893_);
lean_ctor_set(v___x_905_, 1, v___x_899_);
v_entries_906_ = lean_array_fset(v_entries_891_, v_lastIdx_904_, v___x_905_);
lean_dec(v_lastIdx_904_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v_entries_906_);
v___x_908_ = v___x_896_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_entries_906_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_indexes_892_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(lean_object* v_x_913_){
_start:
{
switch(lean_obj_tag(v_x_913_))
{
case 0:
{
lean_object* v_query_914_; 
v_query_914_ = lean_ctor_get(v_x_913_, 1);
lean_inc(v_query_914_);
return v_query_914_;
}
case 1:
{
lean_object* v_uri_915_; lean_object* v_query_916_; 
v_uri_915_ = lean_ctor_get(v_x_913_, 0);
v_query_916_ = lean_ctor_get(v_uri_915_, 3);
lean_inc(v_query_916_);
return v_query_916_;
}
default: 
{
lean_object* v___x_917_; 
v___x_917_ = lean_box(0);
return v___x_917_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f___boxed(lean_object* v_x_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v_x_918_);
lean_dec(v_x_918_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(lean_object* v_ref_920_, uint8_t v_isCrossOrigin_921_, lean_object* v_basePath_922_, lean_object* v_baseQuery_923_, lean_object* v_currentScheme_924_){
_start:
{
lean_object* v___y_926_; lean_object* v___y_927_; 
if (lean_obj_tag(v_ref_920_) == 0)
{
lean_object* v_uri_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_972_; 
lean_dec_ref(v_currentScheme_924_);
lean_dec(v_baseQuery_923_);
lean_dec_ref(v_basePath_922_);
v_uri_930_ = lean_ctor_get(v_ref_920_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v_ref_920_);
if (v_isSharedCheck_972_ == 0)
{
v___x_932_ = v_ref_920_;
v_isShared_933_ = v_isSharedCheck_972_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_uri_930_);
lean_dec(v_ref_920_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_972_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_scheme_934_; lean_object* v_authority_935_; lean_object* v_path_936_; lean_object* v_query_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_970_; 
v_scheme_934_ = lean_ctor_get(v_uri_930_, 0);
v_authority_935_ = lean_ctor_get(v_uri_930_, 1);
v_path_936_ = lean_ctor_get(v_uri_930_, 2);
v_query_937_ = lean_ctor_get(v_uri_930_, 3);
v_isSharedCheck_970_ = !lean_is_exclusive(v_uri_930_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; 
v_unused_971_ = lean_ctor_get(v_uri_930_, 4);
lean_dec(v_unused_971_);
v___x_939_ = v_uri_930_;
v_isShared_940_ = v_isSharedCheck_970_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_query_937_);
lean_inc(v_path_936_);
lean_inc(v_authority_935_);
lean_inc(v_scheme_934_);
lean_dec(v_uri_930_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_970_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___y_942_; 
if (lean_obj_tag(v_authority_935_) == 0)
{
v___y_942_ = v_authority_935_;
goto v___jp_941_;
}
else
{
lean_object* v_val_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_969_; 
v_val_951_ = lean_ctor_get(v_authority_935_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v_authority_935_);
if (v_isSharedCheck_969_ == 0)
{
v___x_953_ = v_authority_935_;
v_isShared_954_ = v_isSharedCheck_969_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_val_951_);
lean_dec(v_authority_935_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_969_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_host_955_; lean_object* v_port_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_967_; 
v_host_955_ = lean_ctor_get(v_val_951_, 1);
v_port_956_ = lean_ctor_get(v_val_951_, 2);
v_isSharedCheck_967_ = !lean_is_exclusive(v_val_951_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; 
v_unused_968_ = lean_ctor_get(v_val_951_, 0);
lean_dec(v_unused_968_);
v___x_958_ = v_val_951_;
v_isShared_959_ = v_isSharedCheck_967_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_port_956_);
lean_inc(v_host_955_);
lean_dec(v_val_951_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_967_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_960_ = lean_box(0);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_960_);
v___x_962_ = v___x_958_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_host_955_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_port_956_);
v___x_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_964_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v___x_962_);
v___x_964_ = v___x_953_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
v___y_942_ = v___x_964_;
goto v___jp_941_;
}
}
}
}
}
v___jp_941_:
{
if (v_isCrossOrigin_921_ == 0)
{
lean_object* v___x_943_; 
lean_dec(v___y_942_);
lean_del_object(v___x_939_);
lean_dec_ref(v_scheme_934_);
lean_del_object(v___x_932_);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v_path_936_);
lean_ctor_set(v___x_943_, 1, v_query_937_);
return v___x_943_;
}
else
{
lean_object* v___x_944_; lean_object* v_stripped_946_; 
v___x_944_ = lean_box(0);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 4, v___x_944_);
lean_ctor_set(v___x_939_, 1, v___y_942_);
v_stripped_946_ = v___x_939_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_scheme_934_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___y_942_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_path_936_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_query_937_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v___x_944_);
v_stripped_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set_tag(v___x_932_, 1);
lean_ctor_set(v___x_932_, 0, v_stripped_946_);
v___x_948_ = v___x_932_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_stripped_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
}
}
else
{
lean_object* v_ref_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1014_; 
v_ref_973_ = lean_ctor_get(v_ref_920_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_ref_920_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_975_ = v_ref_920_;
v_isShared_976_ = v_isSharedCheck_1014_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_ref_973_);
lean_dec(v_ref_920_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1014_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_authority_977_; lean_object* v_path_978_; lean_object* v_query_979_; lean_object* v___y_981_; uint8_t v___y_982_; 
v_authority_977_ = lean_ctor_get(v_ref_973_, 0);
lean_inc(v_authority_977_);
v_path_978_ = lean_ctor_get(v_ref_973_, 1);
lean_inc_ref(v_path_978_);
v_query_979_ = lean_ctor_get(v_ref_973_, 2);
lean_inc(v_query_979_);
lean_dec_ref(v_ref_973_);
if (lean_obj_tag(v_authority_977_) == 0)
{
uint8_t v___x_983_; lean_object* v___y_985_; 
lean_del_object(v___x_975_);
lean_dec_ref(v_currentScheme_924_);
v___x_983_ = l_Std_Http_URI_Path_isEmpty(v_path_978_);
if (v___x_983_ == 0)
{
uint8_t v_absolute_986_; 
v_absolute_986_ = lean_ctor_get_uint8(v_path_978_, sizeof(void*)*1);
if (v_absolute_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = l_Std_Http_URI_Path_parent(v_basePath_922_);
v___x_988_ = l_Std_Http_URI_Path_join(v___x_987_, v_path_978_);
lean_dec_ref(v_path_978_);
v___y_985_ = v___x_988_;
goto v___jp_984_;
}
else
{
lean_dec_ref(v_basePath_922_);
v___y_985_ = v_path_978_;
goto v___jp_984_;
}
}
else
{
lean_dec_ref(v_path_978_);
v___y_985_ = v_basePath_922_;
goto v___jp_984_;
}
v___jp_984_:
{
if (v___x_983_ == 0)
{
v___y_981_ = v___y_985_;
v___y_982_ = v___x_983_;
goto v___jp_980_;
}
else
{
if (lean_obj_tag(v_query_979_) == 0)
{
v___y_981_ = v___y_985_;
v___y_982_ = v___x_983_;
goto v___jp_980_;
}
else
{
lean_dec(v_baseQuery_923_);
v___y_926_ = v___y_985_;
v___y_927_ = v_query_979_;
goto v___jp_925_;
}
}
}
}
else
{
lean_dec(v_baseQuery_923_);
lean_dec_ref(v_basePath_922_);
if (v_isCrossOrigin_921_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec_ref_known(v_authority_977_, 1);
lean_del_object(v___x_975_);
lean_dec_ref(v_currentScheme_924_);
v___x_989_ = l_Std_Http_URI_Path_normalize(v_path_978_);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v_query_979_);
return v___x_990_;
}
else
{
lean_object* v_val_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1013_; 
v_val_991_ = lean_ctor_get(v_authority_977_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_authority_977_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_993_ = v_authority_977_;
v_isShared_994_ = v_isSharedCheck_1013_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_val_991_);
lean_dec(v_authority_977_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1013_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v_host_995_; lean_object* v_port_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1011_; 
v_host_995_ = lean_ctor_get(v_val_991_, 1);
v_port_996_ = lean_ctor_get(v_val_991_, 2);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_val_991_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v_val_991_, 0);
lean_dec(v_unused_1012_);
v___x_998_ = v_val_991_;
v_isShared_999_ = v_isSharedCheck_1011_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_port_996_);
lean_inc(v_host_995_);
lean_dec(v_val_991_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1011_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; lean_object* v_stripped_1002_; 
v___x_1000_ = lean_box(0);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1000_);
v_stripped_1002_ = v___x_998_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_host_995_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v_port_996_);
v_stripped_1002_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1004_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v_stripped_1002_);
v___x_1004_ = v___x_993_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_stripped_1002_);
v___x_1004_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v_af_1005_; lean_object* v___x_1007_; 
v_af_1005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_af_1005_, 0, v_currentScheme_924_);
lean_ctor_set(v_af_1005_, 1, v___x_1004_);
lean_ctor_set(v_af_1005_, 2, v_path_978_);
lean_ctor_set(v_af_1005_, 3, v_query_979_);
lean_ctor_set(v_af_1005_, 4, v___x_1000_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v_af_1005_);
v___x_1007_ = v___x_975_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_af_1005_);
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
}
v___jp_980_:
{
if (v___y_982_ == 0)
{
lean_dec(v_baseQuery_923_);
v___y_926_ = v___y_981_;
v___y_927_ = v_query_979_;
goto v___jp_925_;
}
else
{
lean_dec(v_query_979_);
v___y_926_ = v___y_981_;
v___y_927_ = v_baseQuery_923_;
goto v___jp_925_;
}
}
}
}
v___jp_925_:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = l_Std_Http_URI_Path_normalize(v___y_926_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___y_927_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget___boxed(lean_object* v_ref_1015_, lean_object* v_isCrossOrigin_1016_, lean_object* v_basePath_1017_, lean_object* v_baseQuery_1018_, lean_object* v_currentScheme_1019_){
_start:
{
uint8_t v_isCrossOrigin_boxed_1020_; lean_object* v_res_1021_; 
v_isCrossOrigin_boxed_1020_ = lean_unbox(v_isCrossOrigin_1016_);
v_res_1021_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v_ref_1015_, v_isCrossOrigin_boxed_1020_, v_basePath_1017_, v_baseQuery_1018_, v_currentScheme_1019_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___lam__0(lean_object* v___x_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Std_Http_URI_Parser_parseURIReference(v___x_1025_, v___y_1026_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_pos_1028_; lean_object* v_array_1029_; lean_object* v_idx_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v_pos_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_pos_1028_);
v_array_1029_ = lean_ctor_get(v_pos_1028_, 0);
v_idx_1030_ = lean_ctor_get(v_pos_1028_, 1);
v___x_1031_ = lean_byte_array_size(v_array_1029_);
v___x_1032_ = lean_nat_dec_lt(v_idx_1030_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_dec(v_pos_1028_);
return v___x_1027_;
}
else
{
lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1040_; 
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; lean_object* v_unused_1042_; 
v_unused_1041_ = lean_ctor_get(v___x_1027_, 1);
lean_dec(v_unused_1041_);
v_unused_1042_ = lean_ctor_get(v___x_1027_, 0);
lean_dec(v_unused_1042_);
v___x_1034_ = v___x_1027_;
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
else
{
lean_dec(v___x_1027_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___lam__0___closed__1));
if (v_isShared_1035_ == 0)
{
lean_ctor_set_tag(v___x_1034_, 1);
lean_ctor_set(v___x_1034_, 1, v___x_1036_);
v___x_1038_ = v___x_1034_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_pos_1028_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
return v___x_1027_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect(lean_object* v_current_1055_, lean_object* v_request_1056_, uint8_t v_bodyReplayable_1057_, uint8_t v_onlySafeRedirects_1058_, uint8_t v_responseVersion_1059_, lean_object* v_status_1060_, lean_object* v_responseHeaders_1061_){
_start:
{
lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; uint8_t v___y_1066_; uint8_t v___y_1067_; lean_object* v___y_1068_; uint8_t v___y_1069_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; uint8_t v___y_1080_; uint8_t v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1085_; uint8_t v___y_1086_; uint8_t v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; uint8_t v___y_1090_; uint8_t v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1098_; uint8_t v___y_1099_; uint8_t v___y_1100_; uint8_t v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; uint8_t v___y_1104_; uint8_t v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1110_; uint8_t v___y_1111_; uint8_t v___y_1112_; uint8_t v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; uint8_t v___y_1116_; uint8_t v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1122_; uint8_t v___y_1123_; uint8_t v___y_1124_; uint8_t v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; uint8_t v___y_1128_; uint8_t v___y_1129_; lean_object* v___y_1130_; uint8_t v___y_1131_; uint8_t v___y_1134_; lean_object* v___y_1135_; uint8_t v___y_1136_; uint8_t v___y_1137_; uint8_t v___y_1138_; lean_object* v___y_1139_; uint8_t v___y_1140_; uint8_t v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1145_; uint8_t v___y_1146_; uint8_t v___y_1147_; uint8_t v___y_1148_; uint8_t v___y_1149_; lean_object* v___y_1150_; uint8_t v___y_1151_; lean_object* v___y_1152_; uint8_t v___y_1153_; lean_object* v___y_1154_; uint8_t v___y_1158_; lean_object* v___y_1159_; uint8_t v___y_1160_; uint8_t v___y_1161_; uint8_t v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; uint8_t v___y_1165_; uint8_t v___y_1166_; lean_object* v___y_1167_; uint8_t v___y_1168_; uint8_t v___y_1169_; lean_object* v___y_1173_; uint8_t v___y_1174_; uint8_t v___y_1175_; uint8_t v___y_1176_; uint8_t v___y_1177_; uint8_t v___y_1178_; lean_object* v___y_1179_; uint8_t v___y_1180_; lean_object* v___y_1181_; uint8_t v___y_1182_; lean_object* v___y_1183_; uint8_t v___y_1184_; uint8_t v___y_1186_; lean_object* v___y_1187_; uint8_t v___y_1188_; uint8_t v___y_1189_; uint8_t v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; uint8_t v___y_1193_; uint8_t v___y_1194_; lean_object* v___y_1195_; uint8_t v___y_1196_; lean_object* v___y_1200_; uint8_t v___y_1201_; uint8_t v___y_1202_; uint8_t v___y_1203_; uint8_t v___y_1204_; uint8_t v___y_1205_; lean_object* v___y_1206_; uint8_t v___y_1207_; lean_object* v___y_1208_; uint8_t v___y_1209_; lean_object* v___y_1210_; uint8_t v___y_1212_; lean_object* v___y_1213_; uint8_t v___y_1214_; uint8_t v___y_1215_; uint8_t v___y_1216_; uint8_t v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; uint8_t v___y_1220_; uint8_t v___y_1221_; lean_object* v___y_1222_; uint8_t v___y_1223_; uint8_t v___y_1227_; lean_object* v___y_1228_; uint8_t v___y_1229_; uint8_t v___y_1230_; uint8_t v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; uint8_t v___y_1234_; uint8_t v___y_1235_; lean_object* v___y_1236_; uint8_t v___y_1237_; uint8_t v___y_1243_; lean_object* v___y_1244_; uint8_t v___y_1245_; uint8_t v___y_1246_; uint8_t v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; uint8_t v___y_1250_; lean_object* v___y_1251_; uint8_t v___y_1252_; uint8_t v___y_1255_; lean_object* v___y_1256_; uint8_t v___y_1257_; uint8_t v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; uint8_t v___y_1261_; lean_object* v___y_1262_; uint8_t v___y_1263_; uint8_t v___y_1266_; lean_object* v___y_1267_; uint8_t v___y_1268_; uint8_t v___y_1269_; uint8_t v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; uint8_t v___y_1273_; lean_object* v___y_1274_; uint8_t v___y_1275_; uint8_t v___y_1276_; uint8_t v___y_1283_; uint8_t v___y_1284_; uint8_t v___y_1285_; uint8_t v___y_1312_; uint8_t v___y_1313_; uint8_t v___y_1331_; uint16_t v___x_1341_; uint16_t v___x_1342_; uint8_t v___x_1343_; 
v___x_1341_ = 300;
v___x_1342_ = l_Std_Http_Status_toCode(v_status_1060_);
v___x_1343_ = lean_uint16_dec_le(v___x_1341_, v___x_1342_);
if (v___x_1343_ == 0)
{
v___y_1331_ = v___x_1343_;
goto v___jp_1330_;
}
else
{
uint16_t v___x_1344_; uint8_t v___x_1345_; 
v___x_1344_ = 400;
v___x_1345_ = lean_uint16_dec_lt(v___x_1342_, v___x_1344_);
v___y_1331_ = v___x_1345_;
goto v___jp_1330_;
}
v___jp_1062_:
{
lean_object* v_scheme_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v_rewrittenTarget_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_scheme_1070_ = lean_ctor_get(v_current_1055_, 0);
lean_inc_ref(v_scheme_1070_);
lean_dec_ref(v_current_1055_);
v___x_1071_ = l_Std_Http_RequestTarget_pathOrRoot(v___y_1064_);
v___x_1072_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_requestTargetQuery_x3f(v___y_1064_);
v_rewrittenTarget_1073_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteTarget(v___y_1068_, v___y_1066_, v___x_1071_, v___x_1072_, v_scheme_1070_);
v___x_1074_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1074_, 0, v___y_1063_);
lean_ctor_set(v___x_1074_, 1, v_rewrittenTarget_1073_);
lean_ctor_set(v___x_1074_, 2, v___y_1065_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*3, v___y_1067_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*3 + 1, v___y_1069_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*3 + 2, v___y_1066_);
v___x_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
v___jp_1076_:
{
uint8_t v___x_1083_; 
v___x_1083_ = 0;
v___y_1063_ = v___y_1077_;
v___y_1064_ = v___y_1078_;
v___y_1065_ = v___y_1079_;
v___y_1066_ = v___y_1080_;
v___y_1067_ = v___y_1081_;
v___y_1068_ = v___y_1082_;
v___y_1069_ = v___x_1083_;
goto v___jp_1062_;
}
v___jp_1084_:
{
uint8_t v___x_1093_; 
v___x_1093_ = l_Std_Http_instBEqMethod_beq(v___y_1091_, v___y_1087_);
if (v___x_1093_ == 0)
{
uint8_t v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = 9;
v___x_1095_ = l_Std_Http_instBEqMethod_beq(v___y_1091_, v___x_1094_);
if (v___x_1095_ == 0)
{
if (v___y_1086_ == 0)
{
uint8_t v___x_1096_; 
v___x_1096_ = 1;
v___y_1063_ = v___y_1085_;
v___y_1064_ = v___y_1088_;
v___y_1065_ = v___y_1089_;
v___y_1066_ = v___y_1090_;
v___y_1067_ = v___y_1091_;
v___y_1068_ = v___y_1092_;
v___y_1069_ = v___x_1096_;
goto v___jp_1062_;
}
else
{
v___y_1077_ = v___y_1085_;
v___y_1078_ = v___y_1088_;
v___y_1079_ = v___y_1089_;
v___y_1080_ = v___y_1090_;
v___y_1081_ = v___y_1091_;
v___y_1082_ = v___y_1092_;
goto v___jp_1076_;
}
}
else
{
v___y_1077_ = v___y_1085_;
v___y_1078_ = v___y_1088_;
v___y_1079_ = v___y_1089_;
v___y_1080_ = v___y_1090_;
v___y_1081_ = v___y_1091_;
v___y_1082_ = v___y_1092_;
goto v___jp_1076_;
}
}
else
{
v___y_1077_ = v___y_1085_;
v___y_1078_ = v___y_1088_;
v___y_1079_ = v___y_1089_;
v___y_1080_ = v___y_1090_;
v___y_1081_ = v___y_1091_;
v___y_1082_ = v___y_1092_;
goto v___jp_1076_;
}
}
v___jp_1097_:
{
if (v_bodyReplayable_1057_ == 0)
{
lean_object* v___x_1107_; 
lean_dec_ref(v___y_1106_);
lean_dec_ref(v___y_1103_);
lean_dec_ref(v___y_1098_);
lean_dec_ref(v_current_1055_);
v___x_1107_ = lean_box(0);
return v___x_1107_;
}
else
{
if (v___y_1100_ == 0)
{
v___y_1085_ = v___y_1098_;
v___y_1086_ = v___y_1099_;
v___y_1087_ = v___y_1101_;
v___y_1088_ = v___y_1102_;
v___y_1089_ = v___y_1103_;
v___y_1090_ = v___y_1104_;
v___y_1091_ = v___y_1105_;
v___y_1092_ = v___y_1106_;
goto v___jp_1084_;
}
else
{
lean_object* v___x_1108_; 
lean_dec_ref(v___y_1106_);
lean_dec_ref(v___y_1103_);
lean_dec_ref(v___y_1098_);
lean_dec_ref(v_current_1055_);
v___x_1108_ = lean_box(0);
return v___x_1108_;
}
}
}
v___jp_1109_:
{
uint8_t v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = 9;
v___x_1120_ = l_Std_Http_instBEqMethod_beq(v___y_1117_, v___x_1119_);
if (v___x_1120_ == 0)
{
v___y_1098_ = v___y_1110_;
v___y_1099_ = v___y_1111_;
v___y_1100_ = v___y_1112_;
v___y_1101_ = v___y_1113_;
v___y_1102_ = v___y_1114_;
v___y_1103_ = v___y_1115_;
v___y_1104_ = v___y_1116_;
v___y_1105_ = v___y_1117_;
v___y_1106_ = v___y_1118_;
goto v___jp_1097_;
}
else
{
if (v___y_1112_ == 0)
{
v___y_1085_ = v___y_1110_;
v___y_1086_ = v___y_1111_;
v___y_1087_ = v___y_1113_;
v___y_1088_ = v___y_1114_;
v___y_1089_ = v___y_1115_;
v___y_1090_ = v___y_1116_;
v___y_1091_ = v___y_1117_;
v___y_1092_ = v___y_1118_;
goto v___jp_1084_;
}
else
{
v___y_1098_ = v___y_1110_;
v___y_1099_ = v___y_1111_;
v___y_1100_ = v___y_1112_;
v___y_1101_ = v___y_1113_;
v___y_1102_ = v___y_1114_;
v___y_1103_ = v___y_1115_;
v___y_1104_ = v___y_1116_;
v___y_1105_ = v___y_1117_;
v___y_1106_ = v___y_1118_;
goto v___jp_1097_;
}
}
}
v___jp_1121_:
{
if (v___y_1131_ == 0)
{
v___y_1085_ = v___y_1122_;
v___y_1086_ = v___y_1123_;
v___y_1087_ = v___y_1125_;
v___y_1088_ = v___y_1126_;
v___y_1089_ = v___y_1127_;
v___y_1090_ = v___y_1128_;
v___y_1091_ = v___y_1129_;
v___y_1092_ = v___y_1130_;
goto v___jp_1084_;
}
else
{
uint8_t v___x_1132_; 
v___x_1132_ = l_Std_Http_instBEqMethod_beq(v___y_1129_, v___y_1125_);
if (v___x_1132_ == 0)
{
v___y_1110_ = v___y_1122_;
v___y_1111_ = v___y_1123_;
v___y_1112_ = v___y_1124_;
v___y_1113_ = v___y_1125_;
v___y_1114_ = v___y_1126_;
v___y_1115_ = v___y_1127_;
v___y_1116_ = v___y_1128_;
v___y_1117_ = v___y_1129_;
v___y_1118_ = v___y_1130_;
goto v___jp_1109_;
}
else
{
if (v___y_1124_ == 0)
{
v___y_1085_ = v___y_1122_;
v___y_1086_ = v___y_1123_;
v___y_1087_ = v___y_1125_;
v___y_1088_ = v___y_1126_;
v___y_1089_ = v___y_1127_;
v___y_1090_ = v___y_1128_;
v___y_1091_ = v___y_1129_;
v___y_1092_ = v___y_1130_;
goto v___jp_1084_;
}
else
{
v___y_1110_ = v___y_1122_;
v___y_1111_ = v___y_1123_;
v___y_1112_ = v___y_1124_;
v___y_1113_ = v___y_1125_;
v___y_1114_ = v___y_1126_;
v___y_1115_ = v___y_1127_;
v___y_1116_ = v___y_1128_;
v___y_1117_ = v___y_1129_;
v___y_1118_ = v___y_1130_;
goto v___jp_1109_;
}
}
}
}
v___jp_1133_:
{
if (v___y_1136_ == 0)
{
v___y_1122_ = v___y_1135_;
v___y_1123_ = v___y_1136_;
v___y_1124_ = v___y_1137_;
v___y_1125_ = v___y_1138_;
v___y_1126_ = v___y_1139_;
v___y_1127_ = v___y_1143_;
v___y_1128_ = v___y_1140_;
v___y_1129_ = v___y_1141_;
v___y_1130_ = v___y_1142_;
v___y_1131_ = v___y_1134_;
goto v___jp_1121_;
}
else
{
v___y_1122_ = v___y_1135_;
v___y_1123_ = v___y_1136_;
v___y_1124_ = v___y_1137_;
v___y_1125_ = v___y_1138_;
v___y_1126_ = v___y_1139_;
v___y_1127_ = v___y_1143_;
v___y_1128_ = v___y_1140_;
v___y_1129_ = v___y_1141_;
v___y_1130_ = v___y_1142_;
v___y_1131_ = v___y_1137_;
goto v___jp_1121_;
}
}
v___jp_1144_:
{
lean_object* v_scrubbed_1155_; 
v_scrubbed_1155_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_scrubHeaders(v___y_1152_, v___y_1151_, v___y_1147_);
if (v___y_1151_ == 0)
{
v___y_1134_ = v___y_1146_;
v___y_1135_ = v___y_1145_;
v___y_1136_ = v___y_1147_;
v___y_1137_ = v___y_1148_;
v___y_1138_ = v___y_1149_;
v___y_1139_ = v___y_1150_;
v___y_1140_ = v___y_1151_;
v___y_1141_ = v___y_1153_;
v___y_1142_ = v___y_1154_;
v___y_1143_ = v_scrubbed_1155_;
goto v___jp_1133_;
}
else
{
lean_object* v___x_1156_; 
lean_inc_ref(v___y_1145_);
v___x_1156_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_rewriteHostHeader(v_scrubbed_1155_, v___y_1145_);
v___y_1134_ = v___y_1146_;
v___y_1135_ = v___y_1145_;
v___y_1136_ = v___y_1147_;
v___y_1137_ = v___y_1148_;
v___y_1138_ = v___y_1149_;
v___y_1139_ = v___y_1150_;
v___y_1140_ = v___y_1151_;
v___y_1141_ = v___y_1153_;
v___y_1142_ = v___y_1154_;
v___y_1143_ = v___x_1156_;
goto v___jp_1133_;
}
}
v___jp_1157_:
{
if (v___y_1169_ == 0)
{
v___y_1145_ = v___y_1159_;
v___y_1146_ = v___y_1158_;
v___y_1147_ = v___y_1160_;
v___y_1148_ = v___y_1161_;
v___y_1149_ = v___y_1162_;
v___y_1150_ = v___y_1163_;
v___y_1151_ = v___y_1165_;
v___y_1152_ = v___y_1164_;
v___y_1153_ = v___y_1166_;
v___y_1154_ = v___y_1167_;
goto v___jp_1144_;
}
else
{
if (v___y_1168_ == 0)
{
lean_object* v___x_1170_; 
lean_dec_ref(v___y_1167_);
lean_dec_ref(v___y_1159_);
lean_dec_ref(v_current_1055_);
v___x_1170_ = lean_box(0);
return v___x_1170_;
}
else
{
if (v___y_1161_ == 0)
{
v___y_1145_ = v___y_1159_;
v___y_1146_ = v___y_1158_;
v___y_1147_ = v___y_1160_;
v___y_1148_ = v___y_1161_;
v___y_1149_ = v___y_1162_;
v___y_1150_ = v___y_1163_;
v___y_1151_ = v___y_1165_;
v___y_1152_ = v___y_1164_;
v___y_1153_ = v___y_1166_;
v___y_1154_ = v___y_1167_;
goto v___jp_1144_;
}
else
{
lean_object* v___x_1171_; 
lean_dec_ref(v___y_1167_);
lean_dec_ref(v___y_1159_);
lean_dec_ref(v_current_1055_);
v___x_1171_ = lean_box(0);
return v___x_1171_;
}
}
}
}
v___jp_1172_:
{
if (v___y_1177_ == 0)
{
v___y_1158_ = v___y_1174_;
v___y_1159_ = v___y_1173_;
v___y_1160_ = v___y_1175_;
v___y_1161_ = v___y_1176_;
v___y_1162_ = v___y_1178_;
v___y_1163_ = v___y_1179_;
v___y_1164_ = v___y_1181_;
v___y_1165_ = v___y_1180_;
v___y_1166_ = v___y_1182_;
v___y_1167_ = v___y_1183_;
v___y_1168_ = v___y_1184_;
v___y_1169_ = v___y_1174_;
goto v___jp_1157_;
}
else
{
v___y_1158_ = v___y_1174_;
v___y_1159_ = v___y_1173_;
v___y_1160_ = v___y_1175_;
v___y_1161_ = v___y_1176_;
v___y_1162_ = v___y_1178_;
v___y_1163_ = v___y_1179_;
v___y_1164_ = v___y_1181_;
v___y_1165_ = v___y_1180_;
v___y_1166_ = v___y_1182_;
v___y_1167_ = v___y_1183_;
v___y_1168_ = v___y_1184_;
v___y_1169_ = v___y_1176_;
goto v___jp_1157_;
}
}
v___jp_1185_:
{
if (v___y_1196_ == 0)
{
v___y_1145_ = v___y_1187_;
v___y_1146_ = v___y_1186_;
v___y_1147_ = v___y_1188_;
v___y_1148_ = v___y_1189_;
v___y_1149_ = v___y_1190_;
v___y_1150_ = v___y_1191_;
v___y_1151_ = v___y_1193_;
v___y_1152_ = v___y_1192_;
v___y_1153_ = v___y_1194_;
v___y_1154_ = v___y_1195_;
goto v___jp_1144_;
}
else
{
if (v_bodyReplayable_1057_ == 0)
{
lean_object* v___x_1197_; 
lean_dec_ref(v___y_1195_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v_current_1055_);
v___x_1197_ = lean_box(0);
return v___x_1197_;
}
else
{
if (v___y_1189_ == 0)
{
v___y_1145_ = v___y_1187_;
v___y_1146_ = v___y_1186_;
v___y_1147_ = v___y_1188_;
v___y_1148_ = v___y_1189_;
v___y_1149_ = v___y_1190_;
v___y_1150_ = v___y_1191_;
v___y_1151_ = v___y_1193_;
v___y_1152_ = v___y_1192_;
v___y_1153_ = v___y_1194_;
v___y_1154_ = v___y_1195_;
goto v___jp_1144_;
}
else
{
lean_object* v___x_1198_; 
lean_dec_ref(v___y_1195_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v_current_1055_);
v___x_1198_ = lean_box(0);
return v___x_1198_;
}
}
}
}
v___jp_1199_:
{
if (v___y_1204_ == 0)
{
v___y_1186_ = v___y_1201_;
v___y_1187_ = v___y_1200_;
v___y_1188_ = v___y_1202_;
v___y_1189_ = v___y_1203_;
v___y_1190_ = v___y_1205_;
v___y_1191_ = v___y_1206_;
v___y_1192_ = v___y_1208_;
v___y_1193_ = v___y_1207_;
v___y_1194_ = v___y_1209_;
v___y_1195_ = v___y_1210_;
v___y_1196_ = v___y_1201_;
goto v___jp_1185_;
}
else
{
v___y_1186_ = v___y_1201_;
v___y_1187_ = v___y_1200_;
v___y_1188_ = v___y_1202_;
v___y_1189_ = v___y_1203_;
v___y_1190_ = v___y_1205_;
v___y_1191_ = v___y_1206_;
v___y_1192_ = v___y_1208_;
v___y_1193_ = v___y_1207_;
v___y_1194_ = v___y_1209_;
v___y_1195_ = v___y_1210_;
v___y_1196_ = v___y_1203_;
goto v___jp_1185_;
}
}
v___jp_1211_:
{
uint8_t v___x_1224_; uint8_t v_isPost_1225_; 
v___x_1224_ = 23;
v_isPost_1225_ = l_Std_Http_instBEqMethod_beq(v___y_1214_, v___x_1224_);
switch(lean_obj_tag(v_status_1060_))
{
case 15:
{
v___y_1173_ = v___y_1213_;
v___y_1174_ = v___y_1212_;
v___y_1175_ = v___y_1215_;
v___y_1176_ = v___y_1216_;
v___y_1177_ = v___y_1223_;
v___y_1178_ = v___y_1217_;
v___y_1179_ = v___y_1218_;
v___y_1180_ = v___y_1220_;
v___y_1181_ = v___y_1219_;
v___y_1182_ = v___y_1221_;
v___y_1183_ = v___y_1222_;
v___y_1184_ = v_isPost_1225_;
goto v___jp_1172_;
}
case 16:
{
v___y_1173_ = v___y_1213_;
v___y_1174_ = v___y_1212_;
v___y_1175_ = v___y_1215_;
v___y_1176_ = v___y_1216_;
v___y_1177_ = v___y_1223_;
v___y_1178_ = v___y_1217_;
v___y_1179_ = v___y_1218_;
v___y_1180_ = v___y_1220_;
v___y_1181_ = v___y_1219_;
v___y_1182_ = v___y_1221_;
v___y_1183_ = v___y_1222_;
v___y_1184_ = v_isPost_1225_;
goto v___jp_1172_;
}
case 21:
{
v___y_1200_ = v___y_1213_;
v___y_1201_ = v___y_1212_;
v___y_1202_ = v___y_1215_;
v___y_1203_ = v___y_1216_;
v___y_1204_ = v___y_1223_;
v___y_1205_ = v___y_1217_;
v___y_1206_ = v___y_1218_;
v___y_1207_ = v___y_1220_;
v___y_1208_ = v___y_1219_;
v___y_1209_ = v___y_1221_;
v___y_1210_ = v___y_1222_;
goto v___jp_1199_;
}
case 22:
{
v___y_1200_ = v___y_1213_;
v___y_1201_ = v___y_1212_;
v___y_1202_ = v___y_1215_;
v___y_1203_ = v___y_1216_;
v___y_1204_ = v___y_1223_;
v___y_1205_ = v___y_1217_;
v___y_1206_ = v___y_1218_;
v___y_1207_ = v___y_1220_;
v___y_1208_ = v___y_1219_;
v___y_1209_ = v___y_1221_;
v___y_1210_ = v___y_1222_;
goto v___jp_1199_;
}
default: 
{
v___y_1145_ = v___y_1213_;
v___y_1146_ = v___y_1212_;
v___y_1147_ = v___y_1215_;
v___y_1148_ = v___y_1216_;
v___y_1149_ = v___y_1217_;
v___y_1150_ = v___y_1218_;
v___y_1151_ = v___y_1220_;
v___y_1152_ = v___y_1219_;
v___y_1153_ = v___y_1221_;
v___y_1154_ = v___y_1222_;
goto v___jp_1144_;
}
}
}
v___jp_1226_:
{
uint8_t v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = 8;
v___x_1239_ = l_Std_Http_instBEqMethod_beq(v___y_1230_, v___x_1238_);
if (v___x_1239_ == 0)
{
uint8_t v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = 9;
v___x_1241_ = l_Std_Http_instBEqMethod_beq(v___y_1230_, v___x_1240_);
v___y_1212_ = v___y_1229_;
v___y_1213_ = v___y_1228_;
v___y_1214_ = v___y_1230_;
v___y_1215_ = v___y_1237_;
v___y_1216_ = v___y_1231_;
v___y_1217_ = v___x_1238_;
v___y_1218_ = v___y_1232_;
v___y_1219_ = v___y_1233_;
v___y_1220_ = v___y_1234_;
v___y_1221_ = v___y_1235_;
v___y_1222_ = v___y_1236_;
v___y_1223_ = v___x_1241_;
goto v___jp_1211_;
}
else
{
v___y_1212_ = v___y_1229_;
v___y_1213_ = v___y_1228_;
v___y_1214_ = v___y_1230_;
v___y_1215_ = v___y_1237_;
v___y_1216_ = v___y_1231_;
v___y_1217_ = v___x_1238_;
v___y_1218_ = v___y_1232_;
v___y_1219_ = v___y_1233_;
v___y_1220_ = v___y_1234_;
v___y_1221_ = v___y_1235_;
v___y_1222_ = v___y_1236_;
v___y_1223_ = v___y_1227_;
goto v___jp_1211_;
}
}
v___jp_1242_:
{
uint8_t v___x_1253_; 
v___x_1253_ = l_Std_Http_instBEqMethod_beq(v___y_1250_, v___y_1246_);
if (v___x_1253_ == 0)
{
v___y_1227_ = v___y_1245_;
v___y_1228_ = v___y_1244_;
v___y_1229_ = v___y_1243_;
v___y_1230_ = v___y_1246_;
v___y_1231_ = v___y_1247_;
v___y_1232_ = v___y_1248_;
v___y_1233_ = v___y_1249_;
v___y_1234_ = v___y_1252_;
v___y_1235_ = v___y_1250_;
v___y_1236_ = v___y_1251_;
v___y_1237_ = v___y_1243_;
goto v___jp_1226_;
}
else
{
v___y_1227_ = v___y_1245_;
v___y_1228_ = v___y_1244_;
v___y_1229_ = v___y_1243_;
v___y_1230_ = v___y_1246_;
v___y_1231_ = v___y_1247_;
v___y_1232_ = v___y_1248_;
v___y_1233_ = v___y_1249_;
v___y_1234_ = v___y_1252_;
v___y_1235_ = v___y_1250_;
v___y_1236_ = v___y_1251_;
v___y_1237_ = v___y_1247_;
goto v___jp_1226_;
}
}
v___jp_1254_:
{
uint8_t v___x_1264_; 
v___x_1264_ = l_Std_Http_URI_instBEqOrigin_beq(v___y_1256_, v_current_1055_);
if (v___x_1264_ == 0)
{
v___y_1243_ = v___y_1257_;
v___y_1244_ = v___y_1256_;
v___y_1245_ = v___y_1255_;
v___y_1246_ = v___y_1258_;
v___y_1247_ = v___y_1263_;
v___y_1248_ = v___y_1259_;
v___y_1249_ = v___y_1260_;
v___y_1250_ = v___y_1261_;
v___y_1251_ = v___y_1262_;
v___y_1252_ = v___y_1257_;
goto v___jp_1242_;
}
else
{
v___y_1243_ = v___y_1257_;
v___y_1244_ = v___y_1256_;
v___y_1245_ = v___y_1255_;
v___y_1246_ = v___y_1258_;
v___y_1247_ = v___y_1263_;
v___y_1248_ = v___y_1259_;
v___y_1249_ = v___y_1260_;
v___y_1250_ = v___y_1261_;
v___y_1251_ = v___y_1262_;
v___y_1252_ = v___y_1263_;
goto v___jp_1242_;
}
}
v___jp_1265_:
{
if (v___y_1276_ == 0)
{
v___y_1255_ = v___y_1268_;
v___y_1256_ = v___y_1267_;
v___y_1257_ = v___y_1266_;
v___y_1258_ = v___y_1269_;
v___y_1259_ = v___y_1271_;
v___y_1260_ = v___y_1272_;
v___y_1261_ = v___y_1273_;
v___y_1262_ = v___y_1274_;
v___y_1263_ = v___y_1275_;
goto v___jp_1254_;
}
else
{
lean_object* v_scheme_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_scheme_1277_ = lean_ctor_get(v___y_1267_, 0);
v___x_1278_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__0));
v___x_1279_ = lean_string_dec_eq(v_scheme_1277_, v___x_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; 
lean_dec_ref(v___y_1274_);
lean_dec_ref(v___y_1267_);
lean_dec_ref(v_current_1055_);
v___x_1280_ = lean_box(0);
return v___x_1280_;
}
else
{
if (v___y_1270_ == 0)
{
v___y_1255_ = v___y_1268_;
v___y_1256_ = v___y_1267_;
v___y_1257_ = v___y_1266_;
v___y_1258_ = v___y_1269_;
v___y_1259_ = v___y_1271_;
v___y_1260_ = v___y_1272_;
v___y_1261_ = v___y_1273_;
v___y_1262_ = v___y_1274_;
v___y_1263_ = v___y_1270_;
goto v___jp_1254_;
}
else
{
lean_object* v___x_1281_; 
lean_dec_ref(v___y_1274_);
lean_dec_ref(v___y_1267_);
lean_dec_ref(v_current_1055_);
v___x_1281_ = lean_box(0);
return v___x_1281_;
}
}
}
}
v___jp_1282_:
{
lean_object* v_entries_1286_; lean_object* v_indexes_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_entries_1286_ = lean_ctor_get(v_responseHeaders_1061_, 0);
v_indexes_1287_ = lean_ctor_get(v_responseHeaders_1061_, 1);
v___x_1288_ = l_Std_Http_Header_Name_location;
v___x_1289_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__1___redArg(v_indexes_1287_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; 
lean_dec_ref(v_current_1055_);
v___x_1290_ = lean_box(0);
return v___x_1290_;
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v_entry_1293_; lean_object* v___x_1294_; lean_object* v_snd_1295_; lean_object* v___f_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1291_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___at___00__private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_nominatedConnectionHeaders_spec__2___redArg(v_indexes_1287_, v___x_1288_);
v___x_1292_ = lean_unsigned_to_nat(0u);
v_entry_1293_ = lean_array_fget(v___x_1291_, v___x_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_array_fget_borrowed(v_entries_1286_, v_entry_1293_);
lean_dec(v_entry_1293_);
v_snd_1295_ = lean_ctor_get(v___x_1294_, 1);
v___f_1296_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__2));
v___x_1297_ = lean_string_to_utf8(v_snd_1295_);
v___x_1298_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1296_, v___x_1297_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v___x_1299_; 
lean_dec_ref_known(v___x_1298_, 1);
lean_dec_ref(v_current_1055_);
v___x_1299_ = lean_box(0);
return v___x_1299_;
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1301_; 
v_a_1300_ = lean_ctor_get(v___x_1298_, 0);
lean_inc_n(v_a_1300_, 2);
lean_dec_ref_known(v___x_1298_, 1);
lean_inc_ref(v_current_1055_);
v___x_1301_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_resolveOrigin(v_current_1055_, v_a_1300_);
if (lean_obj_tag(v___x_1301_) == 1)
{
lean_object* v_val_1302_; uint8_t v_method_1303_; lean_object* v_uri_1304_; lean_object* v_headers_1305_; lean_object* v_scheme_1306_; uint8_t v_newMethod_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_val_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_val_1302_);
lean_dec_ref_known(v___x_1301_, 1);
v_method_1303_ = lean_ctor_get_uint8(v_request_1056_, sizeof(void*)*2);
v_uri_1304_ = lean_ctor_get(v_request_1056_, 0);
v_headers_1305_ = lean_ctor_get(v_request_1056_, 1);
v_scheme_1306_ = lean_ctor_get(v_val_1302_, 0);
v_newMethod_1307_ = l___private_Std_Http_Protocol_H1_Redirect_0__Std_Http_Protocol_H1_RedirectPlan_chooseMethod(v_method_1303_, v_responseVersion_1059_, v_status_1060_);
v___x_1308_ = ((lean_object*)(l_Std_Http_Protocol_H1_decideRedirect___closed__3));
v___x_1309_ = lean_string_dec_eq(v_scheme_1306_, v___x_1308_);
if (v___x_1309_ == 0)
{
v___y_1266_ = v___x_1289_;
v___y_1267_ = v_val_1302_;
v___y_1268_ = v___y_1283_;
v___y_1269_ = v_method_1303_;
v___y_1270_ = v___y_1285_;
v___y_1271_ = v_uri_1304_;
v___y_1272_ = v_headers_1305_;
v___y_1273_ = v_newMethod_1307_;
v___y_1274_ = v_a_1300_;
v___y_1275_ = v___y_1284_;
v___y_1276_ = v___x_1289_;
goto v___jp_1265_;
}
else
{
v___y_1266_ = v___x_1289_;
v___y_1267_ = v_val_1302_;
v___y_1268_ = v___y_1283_;
v___y_1269_ = v_method_1303_;
v___y_1270_ = v___y_1285_;
v___y_1271_ = v_uri_1304_;
v___y_1272_ = v_headers_1305_;
v___y_1273_ = v_newMethod_1307_;
v___y_1274_ = v_a_1300_;
v___y_1275_ = v___y_1284_;
v___y_1276_ = v___y_1285_;
goto v___jp_1265_;
}
}
else
{
lean_object* v___x_1310_; 
lean_dec(v___x_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_current_1055_);
v___x_1310_ = lean_box(0);
return v___x_1310_;
}
}
}
}
v___jp_1311_:
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = lean_box(19);
v___x_1315_ = l_Std_Http_instBEqStatus_beq(v_status_1060_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = lean_box(20);
v___x_1317_ = l_Std_Http_instBEqStatus_beq(v_status_1060_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = lean_box(18);
v___x_1319_ = l_Std_Http_instBEqStatus_beq(v_status_1060_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = lean_box(14);
v___x_1321_ = l_Std_Http_instBEqStatus_beq(v_status_1060_, v___x_1320_);
if (v___x_1321_ == 0)
{
if (v_onlySafeRedirects_1058_ == 0)
{
v___y_1283_ = v___y_1312_;
v___y_1284_ = v___y_1313_;
v___y_1285_ = v___y_1313_;
goto v___jp_1282_;
}
else
{
uint8_t v_method_1322_; uint8_t v___x_1323_; 
v_method_1322_ = lean_ctor_get_uint8(v_request_1056_, sizeof(void*)*2);
v___x_1323_ = l_Std_Http_Method_isSafe(v_method_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_dec_ref(v_current_1055_);
v___x_1324_ = lean_box(0);
return v___x_1324_;
}
else
{
if (v___x_1321_ == 0)
{
v___y_1283_ = v___y_1312_;
v___y_1284_ = v___y_1313_;
v___y_1285_ = v___x_1321_;
goto v___jp_1282_;
}
else
{
lean_object* v___x_1325_; 
lean_dec_ref(v_current_1055_);
v___x_1325_ = lean_box(0);
return v___x_1325_;
}
}
}
}
else
{
lean_object* v___x_1326_; 
lean_dec_ref(v_current_1055_);
v___x_1326_ = lean_box(0);
return v___x_1326_;
}
}
else
{
lean_object* v___x_1327_; 
lean_dec_ref(v_current_1055_);
v___x_1327_ = lean_box(0);
return v___x_1327_;
}
}
else
{
lean_object* v___x_1328_; 
lean_dec_ref(v_current_1055_);
v___x_1328_ = lean_box(0);
return v___x_1328_;
}
}
else
{
lean_object* v___x_1329_; 
lean_dec_ref(v_current_1055_);
v___x_1329_ = lean_box(0);
return v___x_1329_;
}
}
v___jp_1330_:
{
if (v___y_1331_ == 0)
{
lean_object* v___x_1332_; 
lean_dec_ref(v_current_1055_);
v___x_1332_ = lean_box(0);
return v___x_1332_;
}
else
{
uint8_t v___x_1333_; uint8_t v___x_1334_; uint8_t v___x_1335_; 
v___x_1333_ = 0;
v___x_1334_ = 0;
v___x_1335_ = l_Std_Http_instBEqVersion_beq(v_responseVersion_1059_, v___x_1334_);
if (v___x_1335_ == 0)
{
v___y_1312_ = v___y_1331_;
v___y_1313_ = v___x_1333_;
goto v___jp_1311_;
}
else
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = lean_box(15);
v___x_1337_ = l_Std_Http_instBEqStatus_beq(v_status_1060_, v___x_1336_);
if (v___x_1337_ == 0)
{
if (v___x_1335_ == 0)
{
v___y_1312_ = v___y_1331_;
v___y_1313_ = v___x_1333_;
goto v___jp_1311_;
}
else
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = lean_box(16);
v___x_1339_ = l_Std_Http_instBEqStatus_beq(v_status_1060_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; 
lean_dec_ref(v_current_1055_);
v___x_1340_ = lean_box(0);
return v___x_1340_;
}
else
{
v___y_1312_ = v___y_1331_;
v___y_1313_ = v___x_1333_;
goto v___jp_1311_;
}
}
}
else
{
v___y_1312_ = v___y_1331_;
v___y_1313_ = v___x_1333_;
goto v___jp_1311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_decideRedirect___boxed(lean_object* v_current_1346_, lean_object* v_request_1347_, lean_object* v_bodyReplayable_1348_, lean_object* v_onlySafeRedirects_1349_, lean_object* v_responseVersion_1350_, lean_object* v_status_1351_, lean_object* v_responseHeaders_1352_){
_start:
{
uint8_t v_bodyReplayable_boxed_1353_; uint8_t v_onlySafeRedirects_boxed_1354_; uint8_t v_responseVersion_boxed_1355_; lean_object* v_res_1356_; 
v_bodyReplayable_boxed_1353_ = lean_unbox(v_bodyReplayable_1348_);
v_onlySafeRedirects_boxed_1354_ = lean_unbox(v_onlySafeRedirects_1349_);
v_responseVersion_boxed_1355_ = lean_unbox(v_responseVersion_1350_);
v_res_1356_ = l_Std_Http_Protocol_H1_decideRedirect(v_current_1346_, v_request_1347_, v_bodyReplayable_boxed_1353_, v_onlySafeRedirects_boxed_1354_, v_responseVersion_boxed_1355_, v_status_1351_, v_responseHeaders_1352_);
lean_dec_ref(v_responseHeaders_1352_);
lean_dec(v_status_1351_);
lean_dec_ref(v_request_1347_);
return v_res_1356_;
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
